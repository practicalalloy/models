module leaderelection

open util/ordering[Node]

abstract sig Type {}
one sig Candidate, Elect extends Type {}

sig Node {
  succ : one Node,
  var inbox : Type -> Node
}

fun Elected : set Node {
  { n : Node | once (before Candidate -> n in n.inbox and Candidate -> n not in n.inbox) }
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
  historically Candidate -> n not in n.succ.inbox // guard
  n.succ.inbox' = n.succ.inbox + Candidate -> n   // effect on n.succ.inbox
  all n2 : Node - n.succ | n2.inbox' = n2.inbox   // effect on the outboxes of other nodes
}

pred processMessage [n : Node, i : Node, t : Type] {
  t -> i in n.inbox                                 // guard

  n.inbox' = n.inbox - t -> i                       // effect on n.inbox
  all n2 : Node - n - n.succ | n2.inbox' = n2.inbox // effect on the inboxes of other nodes
}

pred processCandidate[n : Node, i : Node] {
  processMessage[n,i,Candidate]

  gt[i,n] implies n.succ.inbox' = n.succ.inbox + Candidate -> i // effect on n.succ.inbox
          else    i = n and n.succ != n implies n.succ.inbox' = n.succ.inbox + Elect -> n
          else    n.succ != n implies n.succ.inbox' = n.succ.inbox
}

pred processElected[n : Node, i : Node] {
  processMessage[n,i,Elect]

  i != n implies n.succ.inbox' = n.succ.inbox + Elect -> i      // effect on n.succ.inbox
         else    n.succ != n implies n.succ.inbox' = n.succ.inbox

}

pred stutter {
  // no node acts

  inbox'   = inbox
}

fact message_events {
  // possible events
  always (
    stutter or 
      (some n : Node | initiate[n]) or
      (some n : Node, i : Node | Candidate -> i in n.inbox and processCandidate[n,i]) or
      (some n : Node, i : Node | Elect -> i in n.inbox and processElected[n,i])
  )
}

run example {} expect 1
run example3 {} for exactly 3 Node expect 1

run eventually_elected {
  eventually some Elected
} for exactly 3 Node, 20 steps expect 1

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
    eventually always (historically Candidate -> n not in n.succ.inbox or some n.inbox)
    implies
    always eventually (initiate[n] or some i : Type.(n.inbox) | processCandidate[n,i] or processElected[n,i])
  }
}

assert at_least_one_leader_fair {
  fairness implies eventually (some Elected)
}
check at_least_one_leader_fair expect 0
