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

fact no_shared_dirs {
  // A directory cannot be contained in more than one entry
  all d : Dir | lone contents.d
}

fact no_dangling_objects {
  // Every object except the root is contained somewhere
  Name.(Object.contents) = Object - Root
}
