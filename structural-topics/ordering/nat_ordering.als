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
