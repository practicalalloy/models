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

fact transitions_or_stutter {
  // The system must only evolve according to the defined actions
  always (
    upload or
    (some f : File | delete[f] or restore[f]) or
    (some f : File, t : Token | share[f,t]) or
    (some t : Token | download[t]) or
    empty or
    stutter
  )
}

pred empty {
  some trashed           // guard
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

run example {}

assert shared_are_accessible {
  always shared.Token in File - trashed
}
check shared_are_accessible
check shared_are_accessible for 4 but 20 steps
check shared_are_accessible for 4 but 1.. steps

assert restore_undoes_delete {
  always all f : File | (
    delete[f] and after restore[f] implies
    File'' = File and trashed'' = trashed and shared'' = shared
  )
}
check restore_undoes_delete

assert one_download_per_token {
  all t : Token | always (
    download[t] implies
    after always not download[t]
  )
}
check one_download_per_token

assert empty_after_restore {
  always (
    empty implies
    after ((some f : File | delete[f]) releases not empty)
  )
}
check empty_after_restore

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
check non_restored_files_will_disappear
