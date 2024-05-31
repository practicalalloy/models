module filesharing

sig Token {}

sig File {
  var shared : set Token
}
var sig uploaded in File {}
var sig trashed in uploaded {}

fact init {
  // Initially there are no files uploaded nor shared
  no uploaded
  no shared
}

fact transitions {
  // The system either evolves according to the defined actions or stutters
  always (
    (some f : File | upload[f] or delete[f] or restore[f]) or
    (some f : File, t : Token | share[f,t]) or
    (some t : Token | download[t]) or
    empty or
    stutter
  )
} 

let unchanged[x] { x = (x)' }

pred empty {
  no trashed'                    // effect on trashed
  uploaded' = uploaded - trashed // effect on uploaded
  unchanged[shared]              // no effect on shared
}

pred upload [f : File] {
  f not in uploaded        // guard
  uploaded' = uploaded + f // effect on uploaded
  unchanged[trashed]       // no effect on trashed
  unchanged[shared]        // no effect on shared
}

pred delete [f : File] {
  f in uploaded - trashed       // guard
  trashed'  = trashed + f       // effect on trashed
  shared'   = shared - f->Token // effect on shared
  unchanged[uploaded]           // no effect on uploaded
}

pred restore [f : File] {
  f in trashed            // guard
  trashed'  = trashed - f // effect on trashed
  unchanged[uploaded]     // no effect on uploaded
  unchanged[shared]       // no effect on shared
}

pred share [f : File, t : Token] {
  f in uploaded - trashed           // guard
  historically t not in File.shared // guard
  shared' = shared + f->t           // effect on shared
  unchanged[uploaded]               // no effect on uploaded
  unchanged[trashed]                // no effect on trashed
}

pred download [t : Token] {
  some shared.t                // guard 
  shared'   = shared - File->t // effect on shared
  unchanged[uploaded]          // no effect on uploaded
  unchanged[trashed]           // no effect on trashed
}

pred stutter {
  unchanged[uploaded] // no effect on uploaded
  unchanged[trashed]  // no effect on trashed
  unchanged[shared]   // no effect on trashed
}

run example {}

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
  all f : File | always (
    delete[f] implies
    after ((restore[f] or upload[f]) releases not delete[f])
  )
}
check empty_after_restore

let fair [ena, ev] { always ((always (ena)) implies eventually (ev)) }

fact fairness_on_empty { 
  // Trash is periodically emptied
  fair[(some trashed), empty] 
}

assert non_restored_files_will_disappear {
  all f : File | always (
    delete[f] and after always not restore[f] implies
    eventually f not in uploaded
  )
}
check non_restored_files_will_disappear
