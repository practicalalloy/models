/*  
Natural numbers model at the end of the "Analysis scopes" section, "The
predefined ordering module" topic, of the Practical Alloy book.

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