module filesystem

sig Object {}

sig Dir in Object {}
sig File in Object {}

run example {}

run book_instance1 {
  some disj o0, o1 : univ {
    Object = o0 + o1
    Dir = o1
    File = o0
  }
}

run book_instance2 {
  some disj o0 : univ {
    Object = o0
    Dir = o0
    File = o0
  }
}
