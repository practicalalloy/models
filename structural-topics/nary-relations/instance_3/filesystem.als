module filesystem

abstract sig Object {}

sig Dir extends Object {
    contents : Name -> lone Object
}

sig File extends Object {}

one sig Root extends Dir {}

sig Name {}

run example {}
run example {} for 4
run example {} for 4 but exactly 3 Name

fact no_shared_dirs {
  // A directory cannot be contained in more than one entry
  all d : Dir | lone contents.d
}

fact no_dangling_objects {
  // Every object except the root is contained somewhere
  Name.(Object.contents) = Object - Root
}

fun objects : Dir -> Object {
  { d : Dir, o : Object | some d.contents.o }
}

fun descendants [o : Object] : set Object {
  o.^objects
}

run book_example3 {
  some disj o0, o1, o2, o3, o4, o5, o6 : univ {
    Dir = o0 + o1 + o2
    Root = o0
    File = o3
    Name = o4 + o5 + o6
	univ = o0 + o1 + o2 + o3 + o4 + o5 + o6 + Int
    contents = o0 -> o5 -> o2 + o0 -> o6 -> o3 + o2 -> o5 -> o1 + o2 -> o6 -> o3
  }
} for 4
