/*  
Leader election model for the generation of instance 1 of the "Protocol design"
chapter, "Specifying the network configuration" section, of the Practical Alloy
book.

https://practicalalloy.github.io/chapters/protocol-design/index.html#specifying-the-network-configuration
*/

module leaderelection

sig Node {
  succ : one Node
}

run example {} expect 1

run protocol_design_instance_01 {
  some disj n0, n1 : Node {
    Node = n0 + n1
    succ = n0->n1 + n1->n1
  }
} expect 1
