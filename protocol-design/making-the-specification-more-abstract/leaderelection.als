/*  
Leader election model at the end of the "Making the specification more abstract"
section, "Protocol design" chapter, of the Practical Alloy book.

https://practicalalloy.github.io/chapters/protocol-design/index.html#making-the-specification-more-abstract
*/

module leaderelection

sig Node {
  next : lone Node,
  succ : one Node,
  var inbox : set Node
}
one sig first, last in Node {}

fact ordering {
  no next.first and no last.next
  Node-first in first.^next
}

fun Elected : set Node {
  { n : Node | once (before n in n.inbox and n not in n.inbox) }
}

fact ring {
  // succ forms a ring
  all n : Node | Node in n.^succ
}

fact some_node {
  // at least one node
  some Node
}

fact init {
  // initially inbox and outbox are empty
  no inbox
}

pred initiate [n : Node] {
  // node n initiates the protocol

  historically n not in n.succ.inbox   // guard

  inbox' = inbox + n.succ->n           // effect on inbox
}

pred process [n : Node, i : Node] {
  // i is read and processed by node n

  i in n.inbox                                    // guard

  inbox' = inbox - n->i + n.succ->(i & n.^next)   // effect on inbox
}

pred stutter {
  // no node acts

  inbox' = inbox
}

pred node_acts [n : Node] {
  initiate[n] or
  (some i : Node | process[n, i])
}

fact events {
  // possible events
  always (stutter or some n : Node | node_acts[n])
}

run example {} expect 1
run example3 {} for exactly 3 Node expect 1

run eventually_elected {
  eventually some Elected
} for exactly 3 Node expect 1

run eventually_elected_1node {
  eventually some Elected
} for exactly 1 Node expect 1

assert at_most_one_leader {
  always (lone Elected)
}
check at_most_one_leader expect 0
check at_most_one_leader for 4 but 20 steps expect 0
check at_most_one_leader for 4 but 1.. steps expect 0

assert leader_stays_leader {
  always (all n : Elected | always n in Elected)
}
check leader_stays_leader expect 0

assert at_least_one_leader {
  eventually (some Elected)
}
check at_least_one_leader expect 1

pred initiate_enabled [n : Node] {
  historically n not in n.succ.inbox
}
pred process_enabled [n : Node, i : Node] {
  some n.inbox
}

pred node_enabled [n : Node] {
  initiate_enabled[n] or 
  (some i : Node | process_enabled[n, i])
}

pred fairness {
  all n : Node {
    eventually always node_enabled[n]
    implies
    always eventually node_acts[n]
  }
}

assert at_least_one_leader_fair {
  fairness implies eventually (some Elected)
}
check at_least_one_leader_fair expect 0
