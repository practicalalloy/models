module leaderelection

sig Node {
  next : lone Node,
  succ : one Node,
  var inbox : set Node,
  var outbox : set Node
}
one sig first, last in Node {}

fact ordering {
  no next.first and no last.next
  Node-first in first.^next
}

var sig Elected in Node {}

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
  no inbox and no outbox
  // initially there are no elected nodes
  no Elected
}

pred initiate [n : Node] {
  // node n initiates the protocol

  historically n not in n.outbox             // guard

  n.outbox' = n.outbox + n                   // effect on n.outbox
  all m : Node - n | m.outbox' = m.outbox    // effect on the outboxes of other nodes

  inbox' = inbox                             // frame condition on inbox
  Elected' = Elected                         // frame condition on Elected
}

pred send [n : Node, i : Node] {
  // i is sent from node n to its successor

  i in n.outbox                              // guard

  n.outbox' = n.outbox - i                   // effect on n.outbox
  all m : Node - n | m.outbox' = m.outbox    // effect on the outboxes of other nodes

  n.succ.inbox' = n.succ.inbox + i           // effect on n.succ.inbox
  all m : Node - n.succ | m.inbox' = m.inbox // effect on the inboxes of other nodes

  Elected' = Elected                         // frame condition on Elected
}

pred process [n : Node, i : Node] {
  // i is read and processed by node n

  i in n.inbox                                   // guard

  n.inbox' = n.inbox - i                         // effect on n.inbox
  all m : Node - n | m.inbox' = m.inbox          // effect on the inboxes of other nodes

  i in n.^next implies n.outbox' = n.outbox + i  // effect on n.outbox
               else    n.outbox' = n.outbox
  all m : Node - n | m.outbox' = m.outbox        // effect on the outboxes of other nodes

  i = n implies Elected' = Elected + n           // effect on Elected
        else    Elected' = Elected
}

pred stutter {
  // no node acts

  outbox' = outbox
  inbox' = inbox
  Elected' = Elected
}

pred node_acts [n : Node] {
  initiate[n] or
  (some i : Node | send[n,i]) or
  (some i : Node | process[n,i])
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

run book_instance13 {
  eventually some Elected
  some disj n0, n1, n2 : Node {
    Node = n0 + n1 + n2
    succ = n2 -> n0 + n0 -> n1 + n1 -> n2
    next = n0 -> n1 + n2 -> n0
    no Elected
    no inbox
    no outbox; outbox = n1 -> n1
  }
} for exactly 3 Node expect 1
