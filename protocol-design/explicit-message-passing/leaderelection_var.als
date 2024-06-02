module leaderelection

open util/ordering[Node]

var abstract sig Message {
  var payload : one Node
} 
var sig CandidateMsg, ElectedMsg extends Message {}

sig Node {
  succ : one Node,
  var inbox : set Message
}

fun Elected : set Node {
  { n : Node |
    let inbox_candidates = payload.n & CandidateMsg & n.inbox |
      once (before some inbox_candidates and no inbox_candidates) }
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

pred new_message [m : Message, n : Node] {
  Message' = Message + m
  payload' = payload + m -> n
}

pred same_messages {
  Message' = Message
  payload' = payload
}

pred initiate [n : Node] {
  // node n initiates the protocol
  historically no CandidateMsg & payload.n & n.succ.inbox // guard
  some m : (CandidateMsg & payload.n)' {
    new_message[m,n]
    n.succ.inbox' = n.succ.inbox + m                      // effect on n.succ.inbox
    all m : Node - n.succ | m.inbox' = m.inbox            // effect on the outboxes of other nodes
  }
}

pred processMessage [n : Node, m : Message] {
  // m is read by node n

  m in n.inbox                                      // guard

  n.inbox'  = n.inbox - m                          // effect on n.inbox
  all n2 : Node - n - n.succ | n2.inbox' = n2.inbox // effect on the inboxes of other nodes
}

pred processCandidate[n : Node, m : CandidateMsg] {
  processMessage[n,m]

  gt[m.payload,n] implies (n.succ.inbox' = n.succ.inbox + m and same_messages) // effect on n.succ.inbox
        else m.payload = n and n.succ != n implies (some m2 : (ElectedMsg & payload.n)' | new_message[m2,n] and n.succ.inbox' = n.succ.inbox + m2)
        else n.succ != n implies (n.succ.inbox' = n.succ.inbox and same_messages)
}

pred processElected[n : Node, m : ElectedMsg] {
  processMessage[n,m]

  m.payload != n implies n.succ.inbox' = n.succ.inbox + m  // effect on n.succ.inbox
               else    n.succ != n implies n.succ.inbox' = n.succ.inbox

  same_messages
}

pred stutter {
  // no node acts

  inbox'   = inbox
  same_messages
}

fact message_events {
  // possible events
  always (
    stutter or 
	(some n : Node | initiate[n]) or
	(some n : Node, i : ElectedMsg | processElected[n,i]) or
	(some n : Node, i : CandidateMsg| processCandidate[n,i])
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


run example {} expect 1
run example3 {} for exactly 3 Node, 3 Message expect 1

run example3_generator {
  generator
} for exactly 3 Node, 6 Message expect 1

run example3_unique_generator {
  generator
  unique
} for 3 Node, 10 Message expect 1

run eventually_elected {
  eventually some Elected
} for exactly 3 Node, 4 Message, 20 steps expect 1

run example1 {
  eventually some Elected
} for exactly 1 Node, 3 Message expect 1

run bad_example {
  all n : Node | eventually initiate[n]
  eventually some Elected.inbox & ElectedMsg
} for 3 but exactly 3 Node, 20 steps expect 0

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
        let initiate_enabled = (historically no CandidateMsg & payload.n & n.succ.inbox) and (some CandidateMsg & payload.n),
            process_enabled = some n.inbox and (some ElectedMsg & payload.n) |
		eventually always (initiate_enabled or process_enabled)
		implies
		always eventually (initiate[n] or some i : n.inbox | processCandidate[n,i] or processElected[n,i])
	}
}

assert at_least_one_leader_fair {
  fairness implies eventually (some Elected)
}
check at_least_one_leader_fair expect 1

assert at_least_one_leader_fair_gen {
  (generator and fairness) implies eventually (some Elected)
}
check at_least_one_leader_fair_gen expect 0
