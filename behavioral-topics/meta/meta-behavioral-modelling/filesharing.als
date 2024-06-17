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
  // Initially all mutable elements are empty
  all v: var$ | no v.value
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

pred empty {
  no trashed'                    // effect on trashed
  uploaded' = uploaded - trashed // effect on uploaded
  shared'   = shared             // no effect on shared
}

pred upload [f : File] {
  f not in uploaded                            // guard
  uploaded' = uploaded + f                     // effect on uploaded
  all v: var$ - uploaded$ | v.value = v.value' // no effect on anything other than uploaded
}

pred delete [f : File] {
  f in uploaded - trashed       // guard
  trashed'  = trashed + f       // effect on trashed
  shared'   = shared - f->Token // effect on shared
  uploaded' = uploaded          // no effect on uploaded
}

pred restore [f : File] {
  f in trashed                                // guard
  trashed'  = trashed - f                     // effect on trashed
  all v: var$ - trashed$ | v.value = v.value' // no effect on anything other than trashed
}

pred share [f : File, t : Token] {
  f in uploaded - trashed                        // guard
  historically t not in File.shared              // guard
  shared'   = shared + f->t                      // effect on shared
  all v: var$ - File$shared | v.value = v.value' // no effect on anything other than shared
}

pred download [t : Token] {
  some shared.t                                  // guard 
  shared'   = shared - File->t                   // effect on shared
  all v: var$ - File$shared | v.value = v.value' // no effect on anything other than shared}
}

pred stutter {
  all v: var$ | v.value = v.value' // no effect on anything
}

run example {} expect 1

run some_sig {
  some sig$
} for 2 expect 1

run no_empty_config_sigs {
  all s: sig$ & static$ | some s.value
} expect 1

run no_empty_file_fields {
  all f: File$.subfields & static$ | some f.value
} expect 1

run everything_happens {
  all v: var$ | eventually some v.value
} expect 1
