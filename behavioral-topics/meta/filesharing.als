module filesharing

sig Token {}

sig Attribute {}
sig File {
	attributes : set Attribute,
    var shared : set Token
}
sig Text, Binary extends File {}
sig Link extends File {
	link : one File
}

var sig uploaded in File {}
var sig trashed in uploaded {}

fact init {
--   no uploaded
--   no shared
    // Initially all mutable elements are empty
	all v: var$ | no v.value
}

fact transitions_or_stutter {
    // The system either evolves according to the defined actions or stutters
    always (
        (some f : File | upload[f] or delete[f] or restore[f]) or
        (some f : File, t : Token | share[f,t]) or
        (some t : Token | download[t]) or
        empty or
        stutter
    )
}   

pred empty {
    some trashed                        // guard
    no trashed'                         // effect on trashed
    uploaded' = uploaded - trashed      // effect on uploaded
    shared' = shared                    // no effect on shared
}

pred upload [f : File] {
    f not in uploaded                   // guard
    uploaded' = uploaded + f            // effect on uploaded
	all v: var$ - uploaded$ | v.value = v.value' // no effect on anything other than uploaded
--    trashed' = trashed                  // no effect on trashed
--    shared' = shared                    // no effect on shared
}

pred delete [f : File] {
    f in uploaded - trashed             // guard
    trashed' = trashed + f              // effect on trashed
    shared' = shared - f->Token         // effect on shared
    uploaded' = uploaded                // no effect on uploaded
}

pred restore [f : File] {
    f in trashed                        // guard
    trashed' = trashed - f              // effect on trashed
    uploaded' = uploaded                // no effect on uploaded
    shared' = shared                    // no effect on shared
}

pred share [f : File, t : Token] {
    f in uploaded - trashed             // guard
    historically t not in File.shared   // guard
    shared' = shared + f->t             // effect on shared
    uploaded' = uploaded                // no effect on uploaded
    trashed' = trashed                  // no effect on trashed
}

pred download [t : Token] {
    some shared.t                       // guard	
    shared' = shared - File->t          // effect on shared
    uploaded' = uploaded                // no effect on uploaded
    trashed' = trashed                  // no effect on trashed
}

pred stutter {
	all v: var$ | v.value = v.value'

--    uploaded' = uploaded                // no effect on uploaded
--    trashed' = trashed                  // no effect on trashed
--    shared' = shared                    // no effect on trashed
}

run no_empty_config_sigs {
	 all s: sig$ & static$ | some s.value
}

run no_empty_file_fields {
	 all f: File$.subfields & static$ | some f.value
}

fact {
	no iden & ^link
}

run some_sig {
	some sig$
} for 2

run everything_happens {
	all v: var$ | eventually some v.value
}

run example {}

run shared_deleted {
	some f:File | eventually (f in shared.Token and after f in trashed)
} for 2

assert shared_are_accessible {
    always shared.Token in uploaded - trashed
}
check shared_are_accessible
check shared_are_accessible for 4 but 20 steps
check shared_are_accessible for 4 but 1.. steps

assert restore_undoes_delete {
    all f : File | always (
        delete[f] and after restore[f] implies
        uploaded'' = uploaded and trashed'' = trashed and shared'' = shared
    )
}
check restore_undoes_delete

fun downloaded [t : Token] : set File {
    { f : File | once (download[t] and t in f.shared) }
}

assert one_download_per_token {
    all t : Token | always lone downloaded[t]
}

assert empty_after_restore {
    always (
        empty implies
        after ((some f : File | delete[f]) releases not empty)
    )
}
check empty_after_restore

fact fairness_on_empty {
    always (
        always some trashed implies
        eventually empty
    )
}

assert non_restored_files_will_disappear {
    all f : File | always (
        delete[f] and after always not restore[f] implies
        eventually f not in uploaded
    )
}
check non_restored_files_will_disappear
