module leaderelection

sig Node {
  succ : one Node
}

fact ring {
  // succ forms a ring
  all n : Node | Node in n.^succ
}

run example {} expect 1

run book_instance2 {
  some disj n0, n1, n2 : Node {
    Node = n0 + n1 + n2
    succ = n0 -> n2 + n1 -> n0 + n2 -> n1
  }
} expect 1
