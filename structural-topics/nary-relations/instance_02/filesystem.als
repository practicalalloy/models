/*  
File system model for the generation of instance 2 of the "Higher-arity
relations" topic, "Defining relations by comprehension" section, of the
Practical Alloy book.

https://practicalalloy.github.io/book/chapters/structural-topics/topics/nary-relations/index.html#defining-relations-by-comprehension
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

// Show arbitrary instances with the default scope
run example {}
// Show arbitrary instances with scope 4 for top-level signatures
run example {} for 4

run nary_relations_instance_02 {
  some disj r, d0, d1 : Dir, f0 : File, disj n0, n1, n2 : Name {
    Dir      = r + d0 + d1
    Root     = r
    File     = f0
    Name     = n0 + n1 + n2
    contents = r -> n1 -> d1 + r -> n2 -> f0 + d1 -> n1 -> d0 + d1 -> n2 -> f0
  }
} for 4 expect 1