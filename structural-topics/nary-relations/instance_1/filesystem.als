module filesystem

abstract sig Object {}

sig Dir extends Object {
    contents : Name -> Object
}

sig File extends Object {}

one sig Root extends Dir {}

sig Name {}

run example {}
run example {} for 4
run example {} for 4 but exactly 3 Name

run book_example1 {
  some disj o0, o1, o2, o3, o4, o5, o6 : univ {
    Dir = o0 + o1
    Root = o0
    File = o2 + o3
    Name = o4 + o5 + o6
	univ = o0 + o1 + o2 + o3 + o4 + o5 + o6 + Int
    contents = o0 -> o5 -> o1 + o0 -> o6 -> o3 + o1 -> o4 -> o2 + o1 -> o5 -> o0
  }
} for 4
