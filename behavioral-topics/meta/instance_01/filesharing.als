/*   
File sharing app model for the generation of instance 1 of the
"Meta-capabilities" topic, "The Alloy meta-model" section, of the Practical
Alloy book.

https://practicalalloy.github.io/chapters/behavioral-topics/topics/meta/index.html#the-alloy-meta-model
*/

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

run example {} expect 1

run some_sig {
  some sig$
} for 2 expect 1

run meta_instance_01 {
  some sig$
  some l0 : Link, x0 : Text, t0 : Token, a0 : Attribute {
    Link       = l0
    Text       = x0
    no Binary
    Token      = t0
    link       = l0->x0
    attributes = x0->a0
  }
} for 2 expect 1
