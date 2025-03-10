/*  
File sharing app model at the end of the "Quantifying over mutable signatures"
section, "Mutable top-level signatures" topic, of the Practical Alloy book.

https://practicalalloy.github.io/chapters/behavioral-topics/topics/mutable-toplevel-signatures/index.html#quantifying-over-mutable-signatures
*/

module filesharing

sig Token {}

var sig File {
  var shared : set Token
}
var sig trashed in File {}

fact init {
  // Initially there are no files uploaded nor shared
  no File
}

fact transitions {
  // The system must only evolve according to the defined actions
  always (
    upload or
    (some f : File | delete[f] or restore[f]) or
    (some f : File, t : Token | share[f, t]) or
    (some t : Token | download[t]) or
    empty or
    stutter
  )
}

pred empty {
  no trashed'            // effect on trashed
  File' = File - trashed // effect on File
  shared' = shared       // no effect on shared
}

pred upload {
  one File' - File   // effect on File
  trashed' = trashed // no effect on trashed
  shared' = shared   // no effect on shared
}

pred delete [f : File] {
  f in File - trashed           // guard
  trashed'  = trashed + f       // effect on trashed
  shared'   = shared - f->Token // effect on shared
  File' = File                   // no effect on uploaded
}

pred restore [f : File] {
  f in trashed            // guard
  trashed'  = trashed - f // effect on trashed
  File' = File            // no effect on uploaded
  shared'   = shared      // no effect on shared
}

pred share [f : File, t : Token] {
  f in File - trashed               // guard
  historically t not in File.shared // guard
  shared'   = shared + f->t         // effect on shared
  File' = File                      // no effect on uploaded
  trashed'  = trashed               // no effect on trashed
}

pred download [t : Token] {
  some shared.t                // guard 
  shared'   = shared - File->t // effect on shared
  File' = File                 // no effect on uploaded
  trashed'  = trashed          // no effect on trashed
}

pred stutter {
  File' = File        // no effect on uploaded
  trashed'  = trashed // no effect on trashed
  shared'   = shared  // no effect on trashed
}

run example {} expect 1

assert shared_are_accessible {
  always shared.Token in File - trashed
}
check shared_are_accessible expect 0
check shared_are_accessible for 4 but 20 steps expect 0
check shared_are_accessible for 4 but 1.. steps expect 0

assert restore_undoes_delete {
  always all f : File | (
    delete[f] and after restore[f] implies
    File'' = File and trashed'' = trashed and shared'' = shared
  )
}
// A counter-example is expected because the relation shared is modified
// by delete and restore does not recover it
check restore_undoes_delete expect 1

assert one_download_per_token {
  all t : Token | always (
    download[t] implies
    after always not download[t]
  )
}
check one_download_per_token expect 0

assert empty_after_restore {
  always ( all f : File |
    delete[f] implies
    after ((restore[f] or upload) releases not delete[f])
  )
}
check empty_after_restore expect 0

fact fairness_on_empty {
  // Trash is periodically emptied
  always eventually empty
}

assert non_restored_files_will_disappear {
  always ( all f : File {
    delete[f] and after always not restore[f] implies
    eventually f not in File
  } )
}
check non_restored_files_will_disappear expect 0
