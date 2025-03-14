/*  
Leader election model for the generation of instance 12 of the "Protocol design"
chapter, "Verifying the expected properties" section, of the Practical Alloy
book.

https://practicalalloy.github.io/chapters/protocol-design/index.html#verifying-the-expected-properties
*/

module leaderelection

open util/ordering[Id]

sig Id {}

sig Node {
  succ : one Node,
  id : one Id,
  var inbox : set Id,
  var outbox : set Id
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

fact unique_ids {
  // ids are unique
  all i : Id | lone id.i
}

fact init {
  // initially inbox and outbox are empty
  no inbox and no outbox
  // initially there are no elected nodes
  no Elected
}

pred initiate [n : Node] {
  // node n initiates the protocol

  historically n.id not in n.outbox          // guard

  n.outbox' = n.outbox + n.id                // effect on n.outbox
  all m : Node - n | m.outbox' = m.outbox    // effect on the outboxes of other nodes

  inbox' = inbox                             // frame condition on inbox
  Elected' = Elected                         // frame condition on Elected
}

pred send [n : Node, i : Id] {
  // i is sent from node n to its successor

  i in n.outbox                              // guard

  n.outbox' = n.outbox - i                   // effect on n.outbox
  all m : Node - n | m.outbox' = m.outbox    // effect on the outboxes of other nodes

  n.succ.inbox' = n.succ.inbox + i           // effect on n.succ.inbox
  all m : Node - n.succ | m.inbox' = m.inbox // effect on the inboxes of other nodes

  Elected' = Elected                         // frame condition on Elected
}

pred process [n : Node, i : Id] {
  // i is read and processed by node n

  i in n.inbox                                // guard

  n.inbox' = n.inbox - i                       // effect on n.inbox
  all m : Node - n | m.inbox' = m.inbox        // effect on the inboxes of other nodes

  gt[i, n.id] implies n.outbox' = n.outbox + i // effect on n.outbox
              else    n.outbox' = n.outbox
  all m : Node - n | m.outbox' = m.outbox      // effect on the outboxes of other nodes

  i = n.id implies Elected' = Elected + n      // effect on Elected
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
  (some i : Id | send[n, i]) or
  (some i : Id | process[n, i])
}

fact events {
  // possible events
  always (stutter or some n : Node | node_acts[n])
}

run example {} expect 1
run example3 {} for exactly 3 Node, exactly 3 Id expect 1

run eventually_elected {
  eventually some Elected
} for exactly 3 Node, exactly 3 Id expect 1

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

check protocol_design_instance_12 {
  (some n0 : Node, disj i0, i1, i2 : Id {
    Node          = n0
    Id            = i0 + i1 + i2
    succ          = n0->n0
    ordering/next = i0->i1 + i1->i2
    id            = n0->i0
    always no Elected
    always no inbox
    always no outbox
  }) implies eventually (some Elected)
} expect 1
