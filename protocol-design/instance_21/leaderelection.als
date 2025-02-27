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
--check at_most_one_leader for 4 but 20 steps
--check at_most_one_leader for 4 but 1.. steps

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

check book_instance21 {
  (some disj n0, n1, n2: Node {
    Node = n0 + n1 + n2
    succ = n0 -> n2 + n2 -> n1 + n1 -> n0
    next = n0 -> n1 + n1 -> n2
    no inbox
    inbox' = n1 -> 0 -> n2
    inbox''''' = n0 -> 0 -> n2 + n2 -> 0 -> n0 + n2 -> 1 -> n1
    inbox'''''' = n2 -> 0 -> n0 + n2 -> 1 -> n1
  }) implies (fairness implies eventually (some Elected))
} for exactly 3 Node, 2 seq, exactly 9 steps expect 1
