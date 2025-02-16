/*  
File system model at the end of the "Defining relations by comprehension" section,
"Higher-arity relations" topic, of the Practical Alloy book.

https://practicalalloy.github.io/chapters/structural-topics/topics/nary-relations/index.html#defining-relations-by-comprehension
*/

module filesystem

abstract sig Object {}

sig Dir extends Object {
  contents : Name -> lone Object
}

sig File extends Object {}

one sig Root extends Dir {}

sig Name {}

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

fact no_indirect_containment {
  // Directories cannot descend from themselves
  all d : Dir | d not in descendants[d]
}

// Show arbitrary instances with the default scope
run example {}
// Show arbitrary instances with scope 4 for top-level signatures
run example {} for 4

assert no_partitions {
  // Every object is reachable from the root
  all o : Object | reachable[o]
}

// Check that there can be no partitions in a file system within the default scope
check no_partitions
// Check that there can be no partitions in a file system scope 6 for top-level signatures
check no_partitions for 6