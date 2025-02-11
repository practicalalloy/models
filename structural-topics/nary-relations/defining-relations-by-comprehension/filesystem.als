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

pred reachable [o : Object] {
  o in Root + descendants[Root]
}

fact no_indirect_containment {
  // Directories cannot descend from themselves
  all d : Dir | d not in descendants[d]
}

assert no_partitions {
  // Every object is reachable from the root
  all o : Object | reachable[o]
}

fact no_indirect_containment {
  // Directories cannot descend from themselves
  all d : Dir | d not in descendants[d]
}

// Check that there can be no partitions in a file system within the default scope
check no_partitions
// Check that there can be no partitions in a file system scope 6 for top-level signatures
check no_partitions for 6
