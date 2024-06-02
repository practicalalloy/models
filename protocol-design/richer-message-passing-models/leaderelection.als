module leaderelection

open util/ordering[Node]

sig Node {
  succ       : one Node,
  var inbox  : seq Node
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
  historically n not in elems[n.succ.inbox]   // guard
  n.succ.inbox' = add[n.succ.inbox,n]         // effect on n.succ.inbox
  all m : Node - n.succ | m.inbox' = m.inbox  // effect on the outboxes of other nodes
}

pred process [n : Node, i : Node] {
  // i is read and processed by node n
  i in first[n.inbox]                                 // guard
  n.inbox' = rest[n.inbox]                            // effect on n.inbox
  gt[i,n] implies n.succ.inbox' = add[n.succ.inbox,i] // effect on n.succ.inbox
          else    n.succ != n implies n.succ.inbox' = n.succ.inbox
  all m : Node - n - n.succ | m.inbox' = m.inbox      // effect on the inboxes of other nodes
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
--check at_most_one_leader for 4 but 20 steps expect 0
--check at_most_one_leader for 4 but 1.. steps expect 0

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
		eventually always (historically n not in elems[n.succ.inbox] or some n.inbox)
		implies
		always eventually (initiate[n] or some i : elems[n.inbox] | process[n,i])
	}
}

assert at_least_one_leader_fair {
  fairness implies eventually (some Elected)
}
check at_least_one_leader_fair for 3 but 3 seq, 20..23 steps expect 0
check at_least_one_leader_fair for 3 but 2 seq, 1..10 steps expect 1
/*
enum Event { Stutter, Initiate, Process } // event names

fun stutter_happens : set Event {
  { e: Stutter | stutter }
}

fun initiate_happens : Event -> Node {
  { e: Initiate, n: Node | initiate[n] }
}

fun process_happens : Event -> Node -> Node {
  { e: Process, i: Node, n: Node | process[n, i] }
}

fun events : set Event {
  stutter_happens + initiate_happens.Node + (process_happens).Node.Node
}

check at_most_one_event {
  always lone events
} for exactly 3 Node
*/
