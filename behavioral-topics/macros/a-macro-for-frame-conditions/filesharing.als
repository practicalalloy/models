/*  
File sharing app model at the end of the "A macro for frame conditions" section,
"Macro system" topic, of the Practical Alloy book.

https://practicalalloy.github.io/chapters/behavioral-topics/topics/macros/index.html#a-macro-for-frame-conditions
*/

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
    (some f : File, t : Token | share[f, t]) or
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

run example {} expect 1

assert shared_are_accessible {
  always shared.Token in uploaded - trashed
}
check shared_are_accessible expect 0
check shared_are_accessible for 4 but 20 steps expect 0
check shared_are_accessible for 4 but 1.. steps expect 0

assert restore_undoes_delete {
  all f : File | always (
    delete[f] and after restore[f] implies
    uploaded'' = uploaded and trashed'' = trashed and shared'' = shared
  )
}
// A counter-example is expected because the relation shared is modified
// by delete and restore does not recover it
check restore_undoes_delete expect 1

fun downloaded [t : Token] : set File {
  { f : File | once (download[t] and t in f.shared) }
}

assert one_download_per_token {
  all t : Token | always lone downloaded[t]
}
check one_download_per_token expect 0

assert empty_after_restore {
  all f : File | always (
    delete[f] implies
    after ((restore[f] or upload[f]) releases not delete[f])
  )
}
check empty_after_restore expect 0

fact fairness_on_empty {
  // Trash is periodically emptied
  always eventually empty
}

assert non_restored_files_will_disappear {
  all f : File | always (
    delete[f] and after always not restore[f] implies
    eventually f not in uploaded
  )
}
check non_restored_files_will_disappear expect 0

