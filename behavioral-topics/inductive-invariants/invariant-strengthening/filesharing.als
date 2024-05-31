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
		(some f : File | upload[f] or delete[f] or restore[f]) or
		(some f : File, t : Token | share[f,t]) or
		(some t : Token | download[t]) or
		empty or
		stutter
}   

pred traces { 
	init  
	always next
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
    trashed' = trashed                  // no effect on trashed
    shared' = shared                    // no effect on shared
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
    uploaded' = uploaded                // no effect on uploaded
    trashed' = trashed                  // no effect on trashed
    shared' = shared                    // no effect on trashed
}

run example {}

run {
  traces 
  eventually { one shared and no trashed and no uploaded }
} for 10

pred inv_shared_are_accessible {
  shared.Token in uploaded - trashed
}

assert init_inv_shared_are_accessible { 
  init implies inv_shared_are_accessible 
} 

assert pres_inv_shared_are_accessible { 
  (inv_shared_are_accessible and next) implies 
    after inv_shared_are_accessible 
}

check init_inv_shared_are_accessible for 10 but 1 steps
check pres_inv_shared_are_accessible for 10 but 2 steps

assert shared_are_accessible {
  traces implies always inv_shared_are_accessible
}

check shared_are_accessible for 10 but 1.. steps

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

assert pres_inv_shared_are_uploaded { 
  (inv_shared_are_uploaded and next) implies 
    after inv_shared_are_uploaded }

check init_inv_shared_are_uploaded for 10 but 1 steps
check pres_inv_shared_are_uploaded for 10 but 2 steps
check pres_inv_shared_are_uploaded for 1 but 2 steps

assert accessible_is_uploaded { 
  inv_shared_are_accessible implies inv_shared_are_uploaded 
}

check accessible_is_uploaded for 10 but 1 steps
