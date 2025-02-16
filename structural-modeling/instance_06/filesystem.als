/*  
File system model for the generation of instance 6 of the "Structural modeling"
chapter, "Field declaration" section, of the Practical Alloy book.

https://practicalalloy.github.io/chapters/structural-modeling/index.html#field-declaration
*/

module filesystem

abstract sig Object {}

sig Dir extends Object {
  entries : set Entry
}

sig File extends Object {}

one sig Root extends Dir {}

sig Entry {}
sig Name {}

// Show arbitrary instances with the default scope
run example {}
// Show arbitrary instances with scope 4 for top-level signatures
run example {} for 4

run structural_modeling_instance_06 {
  some disj d0, r : Dir, disj e0, e1, e2 : Entry {
    Dir     = d0 + r
    Root    = r
    File    = none
    Entry   = e0 + e1 + e2 
    Name    = none
    entries = d0 -> e0 + d0 -> e1 + r -> e2
  }
} expect 1