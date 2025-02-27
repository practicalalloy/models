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
  { n, i : Node |
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
  // initially inbox and outbox are empty
  no inbox
}

pred initiate [n : Node] {
  // node n initiates the protocol

  historically no CandidateMsg & payload.n & n.succ.inbox          // guard

  some m : CandidateMsg & payload.n | inbox' = inbox + n.succ->m   // effect on inbox
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
  (some m : CandidateMsg | processCandidate[n, m]) or
  (some m : ElectedMsg | processElected[n, m])
}

fact events {
  // possible events
  always (stutter or some n : Node | node_acts[n])
}

run example {} expect 1
run example3 {} for exactly 3 Node expect 1

run eventually_elected {
  eventually some Elected
} for exactly 3 Node, 6 Message expect 1

run eventually_elected_1node {
  eventually some Elected
} for exactly 1 Node, 2 Message expect 1

run book_instance17 {
  some disj n0: Node, disj m1 : ElectedMsg {
    Node = n0
    succ = n0 -> n0
    no CandidateMsg
    ElectedMsg = m1
    payload = m1 -> n0
    no inbox
  }
} expect 1

run book_instance18 {
  some disj n0: Node, disj m1 : CandidateMsg {
    Node = n0
    succ = n0 -> n0
    no ElectedMsg
    CandidateMsg = m1
    payload = m1 -> n0
    no inbox
  }
} expect 1
