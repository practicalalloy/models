/*  
Leader election model at the end of the "Refining the network model" section,
"Protocol design" chapter, of the Practical Alloy book.

https://practicalalloy.github.io/chapters/protocol-design/index.html#refining-the-network-model
*/

module leaderelection

sig Node {
  next : lone Node,
  succ : one Node,
  var inbox : seq Node
}
one sig first, last in Node {}

fact ordering {
  no next.this/first and no last.next
  Node-first in first.^next
}

fun Elected : set Node {
  { n : Node | once (before n in first[n.inbox] and n not in first[n.inbox]) }
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
  // initially inbox are empty
  no inbox
}

pred initiate [n : Node] {
  // node n initiates the protocol

  historically n not in elems[n.succ.inbox]    // guard

  n.succ.inbox' = add[n.succ.inbox, n]         // effect on n.succ.inbox
  all m : Node - n.succ | m.inbox' = m.inbox   // effect on the outboxes of other nodes
}

pred process [n : Node, i : Node] {
  // i is read and processed by node n

  i in first[n.inbox]                                       // guard

  n.inbox' = rest[n.inbox]                                  // effect on n.inbox
  i in n.^next implies n.succ.inbox' = add[n.succ.inbox, i] // effect on n.succ.inbox
               else    n.succ != n implies n.succ.inbox' = n.succ.inbox
  all m : Node - n - n.succ | m.inbox' = m.inbox            // effect on the inboxes of other nodes
}

pred stutter {
  // no node acts

  inbox'   = inbox
}

pred node_acts[n : Node] {
  initiate[n] or
  (some i : Node | process[n, i])
}

fact events {
  // possible events
  always (
    stutter or some n : Node | node_acts[n]
  )
}

run example {} expect 1
run example3 {} for exactly 3 Node expect 1

run eventually_elected {
  eventually some Elected
} for exactly 3 Node expect 1

run example1 {
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
  historically n not in elems[n.succ.inbox] 
}
pred process_enabled [n : Node, i : Node] {
  i in first[n.inbox] 
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
check at_least_one_leader_fair for 3 but 2 seq expect 1
