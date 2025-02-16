/*  
File system model at the end of the "Specifying constraints" section,
"Higher-arity relations" topic, of the Practical Alloy book.

https://practicalalloy.github.io/book/chapters/structural-topics/topics/nary-relations/index.html#specifying-constraints
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

// Show arbitrary instances with the default scope
run example {}
// Show arbitrary instances with scope 4 for top-level signatures
run example {} for 4