/*  
File sharing app model at the end of the "Event-oriented scenario encoding"
section, "Encoding trace scenarios" topic, of the Practical Alloy book.

https://practicalalloy.github.io/chapters/behavioral-topics/topics/scenarios/index.html#event-oriented-scenario-encoding
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

pred two_tokens [f : File, t0, t1 : Token] {
  File  = f
  Token = t0 + t1
}

run scenario_two_shared_stutter {
  some f : File, disj t0, t1 : Token {
    two_tokens[f, t0, t1]

    no uploaded + trashed and no shared;
    uploaded = f and no shared and no trashed;
    uploaded = f and shared = f->t0 and no trashed;
    uploaded = f and shared = f->t0 + f->t1 and no trashed;
    uploaded = f and shared = f->t0 and no trashed;
    uploaded = f and no shared and trashed = f;
    always (no uploaded + trashed and no shared)
  }
} for 1 File, 2 Token

run scenario_two_shared_event {
   some f : File, disj t0, t1 : Token {
      two_tokens[f, t0, t1]

      upload[f]; share[f, t0]; share[f, t1]; download[t0]; delete[f]; empty; always stutter
   }
} for 1 File, 2 Token
