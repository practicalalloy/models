module filesystem

sig Object {}
sig File extends Object {}
sig Dir extends Object {}

run example {}

run book_instance3 {
  some disj o0,o1,o2 : univ {
    Object = o0 + o1 + o2
    Dir = o1
    File = o0
    univ = o0 + o1 + o2 + Int
  }
}
