/*  
Time-stamp model at the end of the "Adding fields to module parameters" section,
"Module system" topic, of the Practical Alloy book.

https://practicalalloy.github.io/chapters/structural-topics/topics/modules/index.html#adding-fields-to-module-parameters
*/

module timestamp[A,T]
open util/ordering[T]

one sig TimeAux {
  aux_time : A -> T
}

fact {
  TimeAux.aux_time in A -> one T
}