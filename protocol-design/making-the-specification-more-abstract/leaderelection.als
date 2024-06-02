module leaderelection

open util/ordering[Node]

sig Node {
  succ : one Node,
  var inbox : set Node
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
  // initially inbox are empty
  no inbox
}

pred initiate [n : Node] {
  // node n initiates the protocol

  historically n not in n.succ.inbox          // guard

  n.succ.inbox' = n.succ.inbox + n            // effect on n.succ.inbox
  all m : Node - n.succ | m.inbox' = m.inbox  // effect on the outboxes of other nodes
}

pred process [n : Node, i : Node] {
  // i is read and processed by node n

  i in n.inbox                                     // guard

  n.inbox' = n.inbox - i                           // effect on n.inbox
  gt[i,n] implies n.succ.inbox' = n.succ.inbox + i // effect on n.succ.inbox
          else    n.succ.inbox' = n.succ.inbox
  all m : Node - n - n.succ | m.inbox' = m.inbox   // effect on the inboxes of other nodes
}

pred stutter {
  // no node acts

  inbox'   = inbox
}

fact events {
  // possible events
  always (
    stutter or
    (some n : Node | initiate[n]) or
    (some n : Node, i : Node | process[n,i])
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

pred fairness {
  all n : Node {
    eventually always (historically n not in n.succ.inbox or some n.inbox)
	implies always eventually (initiate[n] or some i : n.inbox | process[n,i])
  }
}

assert at_least_one_leader_fair {
  fairness implies eventually (some Elected)
}
check at_least_one_leader_fair expect 0
