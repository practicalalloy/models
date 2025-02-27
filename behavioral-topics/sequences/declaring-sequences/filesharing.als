/*  
File sharing app model at the end of the "Declaring sequences" section,
"Sequences" topic, of the Practical Alloy book.

https://practicalalloy.github.io/chapters/behavioral-topics/topics/sequences/index.html#declaring-sequences
*/

module filesharing

sig Token {}
sig File {
  var shared : set Token
}
var sig uploaded in File {}
one sig Trash {
  var trashed : seq uploaded
}

run example {} expect 1
