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

  inbox' = inbox                           // frame condition on inbox
  Elected' = Elected                       // frame condition on Elected
}

pred initiate_no_guard [n : Node] {
  // node n initiates the protocol

  n.outbox' = n.outbox + n.id                // effect on n.outbox
  all m : Node - n | m.outbox' = m.outbox    // effect on the outboxes of other nodes

  inbox' = inbox                             // frame condition on inbox
  Elected' = Elected                         // frame condition on Elected
}

fact always_initiate {
  // possible events
  always (some n : Node | initiate_no_guard[n])
}

run example {} expect 1
run example3 {} for exactly 3 Node, exactly 3 Id expect 1

run book_instance8 {
  some disj n0, n1, n2 : Node, disj i0, i1, i2 : Id {
    Node = n0 + n1 + n2
    Id = i0 + i1 + i2
    succ = n0 -> n1 + n1 -> n2 + n2 -> n0
    next = i0 -> i1 + i1 -> i2
    id = n0 -> i2 + n1 -> i1 + n2 -> i0
    no Elected
    no inbox
    no outbox
    after {
      no Elected
      no inbox
      outbox = n2 -> i0
    }
  }
} for exactly 3 Node, exactly 3 Id expect 1
