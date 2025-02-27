/*  
Time-stamp model for the generation of instance 5 of the "Module system" topic,
"Private declarations" section, of the Practical Alloy book.

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