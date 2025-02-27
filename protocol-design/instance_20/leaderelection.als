module leaderelection

abstract sig Type {}
one sig Candidate, Elect extends Type {}

sig Node {
  succ : one Node,
  next : lone Node,
  var inbox : Type -> Node
}
one sig first, last in Node {}

fact ordering {
  no next.first and no last.next
  Node-first in first.^next
}

fun Elected : Node -> Node {
  { n, i : Node | once (before Elect->i in n.inbox and Elect->i not in n.inbox) }
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

  historically Candidate->n not in n.succ.inbox   // guard

  inbox' = inbox + n.succ->Candidate->n           // effect on inbox
}

pred processElected[n : Node, i : Node] {
  // elected message m is read and processed by node n

  Elect->i in n.inbox   // guard

  inbox' = inbox - n->Elect->i + n.succ->Elect->(i - n)   // effect on inbox
}

pred processCandidate[n : Node, i : Node] {
  // candidate msg m is read and processed by node n

  Candidate->i in n.inbox   // guard

  inbox' = inbox - n->Candidate->i + n.succ->Candidate->(i & n.^next) + n.succ->Elect->(n & i)   // effect on inbox
}

pred stutter {
  // no node acts

  inbox' = inbox
}

pred node_acts [n : Node] {
  initiate[n] or
  (some i : Node | processCandidate[n, i]) or
  (some i : Node | processElected[n, i])
}

fact events {
  // possible events
  always (stutter or some n : Node | node_acts[n])
}

run example {} expect 1
run example3 {} for exactly 3 Node expect 1

run eventually_elected {
  eventually Node = Elected.Node
} for exactly 3 Node expect 1

run eventually_elected_1node {
  eventually Node = Elected.Node
} for exactly 1 Node expect 1

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
  historically Candidate->n not in n.succ.inbox
}
pred processCandidate_enabled [n : Node, i : Node] {
  Candidate->i in n.inbox
}
pred processElected_enabled [n : Node, i : Node] {
  Elect->i in n.inbox
}

pred node_enabled [n : Node] {
  initiate_enabled[n] or
  (some i : Node | processCandidate_enabled[n, i]) or
  (some i : Node | processElected_enabled[n, i])
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
check at_least_one_leader_fair expect 0

run book_instance20 {
  eventually some Elected
  some disj n0, n1, n2: Node {
    Node = n0 + n1 + n2
    succ = n0 -> n1 + n1 -> n2 + n2 -> n0
    next = n2 -> n0 + n0 -> n1
    no inbox
    inbox'''' = n2 -> Elect -> n1
    inbox''''' = n0 -> Elect -> n1
  }
} for exactly 3 Node, exactly 8 steps expect 1
