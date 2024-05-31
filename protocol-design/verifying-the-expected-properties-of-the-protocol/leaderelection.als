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

pred initiate_no_effect [n : Node] {
  // node n initiates the protocol

  inbox'   = inbox                           // frame condition on inbox
  Elected' = Elected                         // frame condition on Elected
}

pred initiate_no_guard [n : Node] {
  // node n initiates the protocol

  n.outbox' = n.outbox + n.id                // effect on n.outbox
  all m : Node - n | m.outbox' = m.outbox    // effect on the outboxes of other nodes

  inbox'   = inbox                           // frame condition on inbox
  Elected' = Elected                         // frame condition on Elected
}

pred initiate [n : Node] {
  // node n initiates the protocol

  historically n.id not in n.outbox          // guard

  n.outbox' = n.outbox + n.id                // effect on n.outbox
  all m : Node - n | m.outbox' = m.outbox    // effect on the outboxes of other nodes

  inbox'   = inbox                           // frame condition on inbox
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

  n.inbox' = n.inbox - i                      // effect on n.inbox
  all m : Node - n | m.inbox' = m.inbox       // effect on the inboxes of other nodes

  gt[i,n.id] implies n.outbox' = n.outbox + i // effect on n.outbox
             else    n.outbox' = n.outbox
  all m : Node - n | m.outbox' = m.outbox     // effect on the outboxes of other nodes

  i = n.id implies Elected' = Elected + n     // effect on Elected
           else Elected' = Elected
}

pred stutter {
  // no node acts

  outbox'  = outbox
  inbox'   = inbox
  Elected' = Elected
}

fact events {
  // possible events
  always (
    stutter or
    (some n : Node | initiate[n]) or
    (some n : Node, i : Id | send[n,i]) or
    (some n : Node, i : Id | process[n,i])
  )
}

run example {}
run example3 {} for exactly 3 Node, exactly 3 Id

run eventually_elected {
  eventually some Elected
} for exactly 3 Node, exactly 3 Id

assert at_most_one_leader {
  always (lone Elected)
}
check at_most_one_leader
check at_most_one_leader for 4 but 20 steps
check at_most_one_leader for 4 but 1.. steps

assert leader_stays_leader {
  always (all n : Elected | always n in Elected)
}
check leader_stays_leader

assert at_least_one_leader {
  eventually (some Elected)
}
check at_least_one_leader

pred fairness {
  all n : Node {
    eventually always (historically n.id not in n.outbox or some n.inbox or some n.outbox)
    implies
    always eventually (initiate[n] or some i : n.inbox | process[n,i] or send[n,i])
  }
}

assert at_least_one_leader_fair {
  fairness implies eventually (some Elected)
}
check at_least_one_leader_fair
