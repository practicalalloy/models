/*  
File sharing app model at the end of the "Declaring top-level signatures"
section, "Mutable top-level signatures" topic, of the Practical Alloy book.

https://practicalalloy.github.io/chapters/behavioral-topics/topics/mutable-toplevel-signatures/index.html#declaring-top-level-signatures
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

run example {} expect 1
