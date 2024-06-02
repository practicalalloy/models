module leaderelection

abstract sig Message {
  payload : one Node
}
sig CandidateMsg, ElectedMsg extends Message {}

sig Node {
  next : lone Node,
  succ : one Node,
  var inbox : set Message
}

one sig first, last in Node {}

fact ordering {
  no next.first and no last.next	
  Node-first in first.^next
}

fun Elected : Node -> Node {
  { n,i : Node |
    let inbox_elected = payload.i & ElectedMsg & n.inbox |
      once (before some inbox_elected and no inbox_elected) }
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

  historically no CandidateMsg & payload.n & n.succ.inbox  // guard

  some m : CandidateMsg & payload.n {
	inbox' = inbox + n.succ->m  // effect on inbox
  }
}

pred processCandidate[n : Node, m : CandidateMsg] {
  // candidate msg m is read and processed by node n

  m in n.inbox   // guard

  m.payload in n.^next implies           inbox' = inbox - n->m + n.succ->m  // effect on inbox
  m.payload in ^next.n implies           inbox' = inbox - n->m
  else some e : ElectedMsg & payload.n | inbox' = inbox - n->m + n.succ->e
}

pred processElected[n : Node, m : ElectedMsg] {
  // elected msg m is read and processed by node n

  m in n.inbox   // guard

  m.payload != n implies inbox' = inbox - n->m + n.succ->m  // effect on inbox
                 else    inbox' = inbox - n->m
}

pred stutter {
  // no node acts

  inbox' = inbox
}

pred node_acts [n : Node] {
  initiate[n] or
  (some m : CandidateMsg | processCandidate[n,m]) or
  (some m : ElectedMsg | processElected[n,m])
}

fact events {
  // possible events
  always (
    stutter or some n : Node | node_acts[n]
  )
}

pred generator {
  all n : Node {
    some m : CandidateMsg | m.payload = n
    some m : ElectedMsg   | m.payload = n
  }
}

pred unique {
  all m1,m2 : CandidateMsg | m1.payload = m2.payload implies m1 = m2
  all m1,m2 : ElectedMsg   | m1.payload = m2.payload implies m1 = m2
}

fact { generator and unique }

run example {} expect 1
run example3 {} for exactly 3 Node, 3 Message expect 1

run example3_generator {
  generator
} for exactly 3 Node, 6 Message, 1 steps

run example3_unique_generator {
  generator
  unique
} for 3 Node, 6 Message, 1 steps

run eventually_elected {
  eventually Node = Elected.Node
} for exactly 3 Node, 2 Message expect 1

run example1 {
  eventually Node = Elected.Node
} for exactly 1 Node, 2 Message expect 1

run bad_example {
  all n : Node | eventually initiate[n]
  eventually Node = Elected.Node
} for 3 but exactly 3 Node, 20 steps expect 0

assert at_most_one_leader {
  always lone Node.Elected
}
check at_most_one_leader expect 0
check at_most_one_leader for 4 but 20 steps expect 0
check at_most_one_leader for 4 but 1.. steps expect 0

assert leader_stays_leader {
  always (all n : Node.Elected | always n in Node.Elected)
}
check leader_stays_leader expect 0

assert at_least_one_leader {
  eventually (Node = Elected.Node)
}
check at_least_one_leader expect 1

pred initiate_enabled [n : Node] {
  historically no CandidateMsg & payload.n & n.succ.inbox
  some CandidateMsg & payload.n
}
pred processCandidate_enabled [n : Node, m : Message] {
  m in n.inbox
  m.payload = n implies some ElectedMsg & payload.n
}
pred processElected_enabled [n : Node, m : Message] {
  m in n.inbox
}

pred node_enabled [n : Node] {
  initiate_enabled[n] or 
  (some m : CandidateMsg | processCandidate_enabled[n,m]) or 
  (some m : ElectedMsg | processElected_enabled[n,m])
}

pred fairness {
  all n : Node {
    eventually always node_enabled[n]
    implies
    always eventually node_acts[n]
  }
}

assert at_least_one_leader_fair {
  fairness implies eventually (Node = Elected.Node)
}
check at_least_one_leader_fair for 3 but 6 Message, 20 steps expect 0

assert at_least_one_leader_fair_gen {
  (generator and fairness) implies eventually (Node = Elected.Node)
}
check at_least_one_leader_fair_gen for 3 but 6 Message, 10 steps expect 0
