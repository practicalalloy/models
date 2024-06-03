module leaderelection

sig Node {
  succ : one Node
}

run example {} expect 1

run book_instance1 {
  some disj n0, n1 : Node {
    Node = n0 + n1
    succ = n0 -> n1 + n1 -> n1
  }
} expect 1
