/*  
Time-stamp model at the end of the "Private declarations" section, "Module
system" topic, of the Practical Alloy book.

https://practicalalloy.github.io/chapters/structural-topics/topics/modules/index.html#private-declarations
*/

module timestamp[A, T]
open util/ordering[T]

private one sig TimeAux {
  aux_time : A -> T
}

fact {
  TimeAux.aux_time in A -> one T
}

fun time : A -> T {
  TimeAux.aux_time
}