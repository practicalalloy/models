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

run example {}
run example3 {} for exactly 3 Node, exactly 3 Id

run book_instance3 {

}
