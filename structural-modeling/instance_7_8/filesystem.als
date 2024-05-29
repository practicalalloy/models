module filesystem

abstract sig Object {}

sig Dir extends Object {
  entries : set Entry
}

sig File extends Object {}

one sig Root extends Dir {}

sig Entry {
  object : one Object,
  name   : one Name
}

sig Name {}

run example {}
run example {} for 4

run book_instance7 {
  some disj o0,o1,o2,o3,o4,o5,o6,o7 : univ {
    Dir = o0 + o1
    Root = o1
    File = o2
    Entry = o3 + o4 + o5 + o6
    Name = o7
    univ = o0 + o1 + o2 + o3 + o4 + o5 + o6 + o7 + Int
    entries = o0 -> o3 + o0 -> o4 + o0 -> o5 + o0 -> o6 + o1 -> o6
    name = o3 -> o7 + o4 -> o7 + o5 -> o7 + o6 -> o7
    object = o3 -> o0 + o4 -> o0 + o5 -> o0 + o6 -> o0
  }
} for 4

run book_instance8 {
  some disj o0,o1,o2,o3,o4,o5,o6,o7 : univ {
    Dir = o0 + o1
    Root = o1
    File = o2
    Entry = o3 + o4 + o5 + o6
    Name = o7
    univ = o0 + o1 + o2 + o3 + o4 + o5 + o6 + o7 + Int
    entries = o0 -> o3 + o0 -> o4 + o0 -> o5 + o0 -> o6 + o1 -> o6
    name = o3 -> o7 + o4 -> o7 + o5 -> o7 + o6 -> o7
    object = o3 -> o0 + o4 -> o0 + o5 -> o0 + o6 -> o0
  }
} for 4
