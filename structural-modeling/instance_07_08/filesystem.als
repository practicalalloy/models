/*  
File system model for the generation of instances 7 and 8 of the "Structural
modeling" chapter, "Field declaration" section, of the Practical Alloy book.

https://practicalalloy.github.io/book/chapters/structural-modeling/index.html#field-declaration
*/

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

// Show arbitrary instances with the default scope
run example {}
// Show arbitrary instances with scope 4 for top-level signatures
run example {} for 4

run structural_design_instance_07 {
  some disj d0, r : Dir, f0 : File, disj e0, e1, e2, e3 : Entry, n0 : Name {
    Dir = d0 + r
    Root = r
    File = f0
    Entry = e0 + e1 + e2 + e3
    Name = n0
    entries = d0 -> e0 + d0 -> e1 + d0 -> e2 + d0 -> e3 + r -> e3
    name = e0 -> n0 + e1 -> n0 + e2 -> n0 + e3 -> n0
    object = e0 -> d0 + e1 -> d0 + e2 -> d0 + e3 -> d0
  }
} for 4 expect 1

run structural_design_instance_08 {
  some disj d0, r : Dir, f0 : File, disj e0, e1, e2, e3 : Entru, n0 : Name {
    Dir = d0 + r
    Root = r
    File = f0
    Entry = e0 + e1 + e2 + e3
    Name = n0
    entries = d0 -> e0 + d0 -> e1 + d0 -> e2 + d0 -> e3 + r -> e3
    name = e0 -> n0 + e1 -> n0 + e2 -> n0 + e3 -> n0
    object = e0 -> d0 + e1 -> d0 + e2 -> d0 + e3 -> d0
  }
} for 4 expect 1