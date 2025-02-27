/*   
File sharing app model for the generation of instances 7 and 8 of the "An idiom
for event depiction" topic, "Depicting events with parameters" section, of the
Practical Alloy book.

https://practicalalloy.github.io/chapters/behavioral-topics/topics/event-depiction/index.html#depicting-events-with-parameters
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

enum Event {
  // event names
  Empty, Upload, Delete, Restore, Share, Download, Stutter
}

fun empty_happens : set Event {
  { e : Empty | empty }
}

fun stutter_happens : set Event {
  { e : Stutter | stutter }
}

fun upload_happens : Event -> File {
  { e : Upload, f : File | upload[f] }
}

fun delete_happens : Event -> File {
  { e : Delete, f : File | delete[f] }
}

fun restore_happens : Event -> File {
  { e : Restore, f : File | restore[f] }
}

fun download_happens : Event -> Token {
  { e : Share, t : Token | download[t] }
}

fun share_happens : Event -> File -> Token {
  { e : Share, f : File, t : Token | share[f, t] }
}

run event_depiction_instance_07_08 {
  some disj f0, f1 : File, disj t0, t1 : Token {
    File  = f0 + f1
    Token = t0 + t1
    upload[f1]; share[f1, t1]; delete[f1]; empty; always stutter
  }
} expect 1
