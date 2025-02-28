/*  
Leader election model for the generation of instance 3 of the "Protocol design"
chapter, "Specifying the network configuration" section, of the Practical Alloy
book.

https://practicalalloy.github.io/chapters/protocol-design/index.html#specifying-the-network-configuration
*/

module leaderelection

open util/ordering[Id]

sig Id {}

sig Node {
  succ : one Node,
  id : one Id
}

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

run example {} expect 1
run example3 {} for exactly 3 Node, exactly 3 Id expect 1

run protocol_design_instance_03 {
  some disj n0, n1, n2 : Node, disj i0, i1, i2 : Id {
    Node = n0 + n1 + n2
    Id   = i0 + i1 + i2
    succ = n0->n1 + n1->n2 + n2->n0
    next = i0->i1 + i1->i2
    id   = n0->i2 + n1->i1 + n2->i0
  }
} for exactly 3 Node, exactly 3 Id expect 1
