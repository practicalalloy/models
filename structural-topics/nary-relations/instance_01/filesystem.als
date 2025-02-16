/*  
File system model for the generation of instance 1 of the "Higher-arity
relations" topic, "Visualizing higher-arity fields" section, of the Practical
Alloy book.

https://practicalalloy.github.io/book/chapters/structural-topics/topics/nary-relations/index.html#declaring-higher-arity-fields
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

run nary_relations_instance_01 {
  some disj r, d0 : Dir, disj f0, f1 : File, disj n0, n1, n2 : Name {
    Dir      = r + d0
    Root     = r
    File     = f0 + f1
    Name     = n0 + n1 + n2
    contents = r -> n1 -> d0 + r -> n2 -> f1 + d0 -> n0 -> f0 + d0 -> n1 -> r
  }
} for 4 expect 1