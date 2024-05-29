module filesystem

abstract sig Object {}

sig Dir extends Object {
  entries : set Entry
}

sig File extends Object {}

one sig Root extends Dir {}

sig Entry {}
sig Name {}

run example {}
run example {} for 4

run book_instance6 {
  some disj o0,o1,o2,o3,o4: univ {
    Dir = o0 + o1
    Root = o1
    File = none
    Entry = o2 + o3 + o4 
    Name = none
    univ = o0 + o1 + o2 + o3 + o4 + Int
    entries = o0 -> o2 + o0 -> o3 + o1 -> o4
  }
}
