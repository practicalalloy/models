/*  
File sharing app model at the end of the "Specifying transition systems"
section, "Behavioral modeling" chapter, of the Practical Alloy book.

https://practicalalloy.github.io/chapters/behavioral-modeling/index.html#specifying-transition-systems
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
  // The system evolves according to the defined actions
  always (
    (some f : File | upload[f] or delete[f] or restore[f]) or
    (some f : File, t : Token | share[f, t]) or
    (some t : Token | download[t]) or
    empty
  )
} 

pred empty {

}

pred upload [f : File] {

}

pred delete [f : File] {

}

pred restore [f : File] {

}

pred share [f : File, t : Token] {

}

pred download [t : Token] {

}
