module filesystem

abstract sig Object {}

sig Dir extends Object {}
sig File extends Object {}

one sig Root extends Dir {}

sig Entry {}
sig Name {}

run example {}
run example {} for 4
run example {} for 4 but 2 Entry, exactly 3 Name

run book_instance4 {
  some disj o0,o1,o2 : univ {
    Dir = o0 + o1 + o2
    Root = o2
    File = none
    univ = o0 + o1 + o2 + Int
  }
}

run book_instance5 {
  some disj o0,o1,o2,o3,o4,o5 : univ {
    Dir = o0 + o1
    Root = o1
    File = none
    Entry = o2 + o3
    Name = o4 + o5
    univ = o0 + o1 + o2 + o3 + o4 + o5 + Int
  }
} for 4
