/*  
File system model at the end of the "Visualizing higher-arity fields" section,
"Higher-arity relations" topic, of the Practical Alloy book.

https://practicalalloy.github.io/chapters/structural-topics/topics/nary-relations/index.html#visualizing-higher-arity-fields
*/

module filesystem

abstract sig Object {}

sig Dir extends Object {
  contents : Name -> Object
}

sig File extends Object {}

one sig Root extends Dir {}

sig Name {}

// Show arbitrary instances with the default scope
run example {}
// Show arbitrary instances with scope 4 for top-level signatures
run example {} for 4