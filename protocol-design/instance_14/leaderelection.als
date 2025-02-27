module leaderelection

sig Node {
  next : lone Node,
  succ : one Node,
  var inbox : set Node
}
one sig first, last in Node {}

fact ordering {
  no next.first and no last.next
  Node-first in first.^next
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
  // initially inbox and outbox are empty
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

  i in n.inbox                                          // guard

  n.inbox' = n.inbox - i                                // effect on n.inbox
  i in n.^next implies n.succ.inbox' = n.succ.inbox + i // effect on n.succ.inbox
               else    n.succ.inbox' = n.succ.inbox
  all m : Node - n - n.succ | m.inbox' = m.inbox        // effect on the inboxes of other nodes
}

pred stutter {
  // no node acts

  inbox' = inbox
}

pred node_acts [n : Node] {
  initiate[n] or
  (some i : Node | process[n, i])
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

run book_instance14 {
  eventually some Elected
  some disj n0, n1, n2 : Node {
    Node = n0 + n1 + n2
    succ = n2 -> n0 + n0 -> n1 + n1 -> n2
    next = n0 -> n1 + n2 -> n0
    no Elected
    no inbox
  }
} for exactly 3 Node expect 1
