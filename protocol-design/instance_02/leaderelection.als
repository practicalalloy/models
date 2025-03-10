/*  
Leader election model for the generation of instance 2 of the "Protocol design"
chapter, "Specifying the network configuration" section, of the Practical Alloy
book.

https://practicalalloy.github.io/chapters/protocol-design/index.html#specifying-the-network-configuration
*/

module leaderelection

sig Node {
  succ : one Node
}

fact ring {
  // succ forms a ring
  all n : Node | Node in n.^succ
}

run example {} expect 1

run protocol_design_instance_02 {
  some disj n0, n1, n2 : Node {
    Node = n0 + n1 + n2
    succ = n0->n2 + n1->n0 + n2->n1
  }
} expect 1
