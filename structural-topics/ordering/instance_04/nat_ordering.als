/*  
Natural numbers model for the generation of instance 4 of the "The predefined
ordering module" topic, "Analysis scopes" section, of the Practical Alloy book.

https://practicalalloy.github.io/book/chapters/structural-topics/topics/ordering/index.html#analysis-scopes
*/

open util/ordering[Nat]

abstract sig Nat {}
sig Even, Odd extends Nat {}

fact {
  all n : Even | n.next in Odd
  all n : Odd | n.next in Even
  first in Even
  last in Odd
}

run example {}
run example {} for 4