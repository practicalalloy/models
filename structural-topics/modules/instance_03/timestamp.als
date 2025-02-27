/*  
Time-stamp model for the generation of instance 3 of the "Module system" topic,
"Adding fields to module parameters" section, of the Practical Alloy book.

https://practicalalloy.github.io/chapters/structural-topics/topics/modules/index.html#adding-fields-to-module-parameters
*/

module timestamp[A, T]
open util/ordering[T]

one sig TimeAux {
  aux_time : A -> T
}

fact {
  TimeAux.aux_time in A -> one T
}