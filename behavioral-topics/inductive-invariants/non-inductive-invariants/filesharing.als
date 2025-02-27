/*  
File sharing app model at the end of the "Non-inductive invariants" section,
"Inductive invariants" topic, of the Practical Alloy book.

https://practicalalloy.github.io/chapters/behavioral-topics/topics/inductive-invariants/index.html#non-inductive-invariants
*/

module filesharing

sig Token {}
sig File {
  var shared : set Token
}
var sig uploaded in File {}
var sig trashed in uploaded {}

pred init {
  // Initially there are no files uploaded nor shared
  no uploaded
  no shared
}

pred next {
  // The system either evolves according to the defined actions or stutters
  (some f : File | upload[f] or delete[f] or restore[f]) or
  (some f : File, t : Token | share[f, t]) or
  (some t : Token | download[t]) or
  empty or
  stutter
} 

pred traces {
  init
  always next
}

pred empty {
  no trashed'                    // effect on trashed
  uploaded' = uploaded - trashed // effect on uploaded
  shared'   = shared             // no effect on shared
}

pred upload [f : File] {
  f not in uploaded        // guard
  uploaded' = uploaded + f // effect on uploaded
  trashed'  = trashed      // no effect on trashed
  shared'   = shared       // no effect on shared
}

pred delete [f : File] {
  f in uploaded - trashed       // guard
  trashed'  = trashed + f       // effect on trashed
  shared'   = shared - f->Token // effect on shared
  uploaded' = uploaded          // no effect on uploaded
}

pred restore [f : File] {
  f in trashed            // guard
  trashed'  = trashed - f // effect on trashed
  uploaded' = uploaded    // no effect on uploaded
  shared'   = shared      // no effect on shared
}

pred share [f : File, t : Token] {
  f in uploaded - trashed           // guard
  historically t not in File.shared // guard
  shared'   = shared + f->t         // effect on shared
  uploaded' = uploaded              // no effect on uploaded
  trashed'  = trashed               // no effect on trashed
}

pred download [t : Token] {
  some shared.t                // guard 
  shared'   = shared - File->t // effect on shared
  uploaded' = uploaded         // no effect on uploaded
  trashed'  = trashed          // no effect on trashed
}

pred stutter {
  uploaded' = uploaded // no effect on uploaded
  trashed'  = trashed  // no effect on trashed
  shared'   = shared   // no effect on trashed
}

run example { traces } expect 1

assert shared_are_accessible {
  traces implies always shared.Token in uploaded - trashed
}
check shared_are_accessible expect 0
check shared_are_accessible for 4 but 20 steps expect 0
check shared_are_accessible for 4 but 1.. steps expect 0
check shared_are_accessible for 10 but 1.. steps

assert restore_undoes_delete {
  traces implies 
  all f : File | always (
    delete[f] and after restore[f] implies
    uploaded'' = uploaded and trashed'' = trashed and shared'' = shared
  )
}
check restore_undoes_delete expect 1

fun downloaded [t : Token] : set File {
  { f : File | once (download[t] and t in f.shared) }
}

assert one_download_per_token {
  traces implies all t : Token | always lone downloaded[t]
}
check one_download_per_token expect 0

assert empty_after_restore {
  traces implies 
  all f : File | always (
    delete[f] implies
    after ((restore[f] or upload[f]) releases not delete[f])
  )
}
check empty_after_restore expect 0

pred fairness_on_empty {
  // Trash is periodically emptied
  always eventually empty
}

assert non_restored_files_will_disappear {
  traces and fairness_on_empty implies 
  all f : File | always (
    delete[f] and after always not restore[f] implies
    eventually f not in uploaded
  )
}
check non_restored_files_will_disappear expect 0

pred inv_shared_are_accessible {
  shared.Token in uploaded - trashed
}

assert init_inv_shared_are_accessible {
  init implies inv_shared_are_accessible
}
check init_inv_shared_are_accessible for 10 but 1 steps expect 0

assert pres_inv_shared_are_accessible {
  (inv_shared_are_accessible and next) implies
    after inv_shared_are_accessible
}
check pres_inv_shared_are_accessible for 10 but 2 steps expect 0

pred inv_shared_are_uploaded {
  shared.Token in uploaded
}

assert shared_are_uploaded {
  traces implies always inv_shared_are_uploaded
}
check shared_are_uploaded for 10 but 1.. steps

assert init_inv_shared_are_uploaded {
  init implies inv_shared_are_uploaded
}
check init_inv_shared_are_uploaded for 10 but 1 steps expect 0

assert pres_inv_shared_are_uploaded {
  (inv_shared_are_uploaded and next) implies
    after inv_shared_are_uploaded
}
check pres_inv_shared_are_uploaded for 10 but 2 steps expect 1
check pres_inv_shared_are_uploaded for 1 but 2 steps expect 1
