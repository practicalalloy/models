module leaderelection

sig Node {
  succ : one Node
}

fact ring {
  // succ forms a ring
  all n : Node | Node in n.^succ
}

run example {}

run book_instance2 {
  // todo

}
