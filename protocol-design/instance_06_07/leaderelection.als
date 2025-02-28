/*  
Leader election model for the generation of instances 6 and 7 of the "Protocol
design" chapter, "Specifying the protocol dynamics" section, of the Practical
Alloy book.

https://practicalalloy.github.io/chapters/protocol-design/index.html#specifying-the-protocol-dynamics
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

run example {} expect 1
run example3 {} for exactly 3 Node, exactly 3 Id expect 1

run protocol_design_instance_06 {
  some disj n0, n1, n2 : Node, disj i0, i1, i2 : Id {
    Node = n0 + n1 + n2
    Id   = i0 + i1 + i2
    succ = n0->n1 + n1->n2 + n2->n0
    next = i0->i1 + i1->i2
    id   = n0->i2 + n1->i1 + n2->i0
    no Elected
    no inbox
    no outbox
  }
} for exactly 3 Node, exactly 3 Id expect 1

run protocol_design_instance_07 {
  some disj n0, n1, n2 : Node, i0, i1, i2 : Id {
    Node = n0 + n1 + n2
    Id   = i0 + i1 + i2
    succ = n0->n1 + n1->n2 + n2->n0
    next = i0->i1 + i1->i2
    id   = n0->i2 + n1->i1 + n2->i0
    no Elected
    no inbox
    no outbox
    after {
      Elected = n1
      inbox   = n0->i1 + n1->i0 + n1->i2 + n2->i1
      outbox  = n0->i0 + n0->i2 + n1->i1 + n2->i0
    }
  }
} for exactly 3 Node, exactly 3 Id expect 1
