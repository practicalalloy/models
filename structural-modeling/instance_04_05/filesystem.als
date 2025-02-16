/*  
File system model for the generation of instances 4 and 5 of the "Structural
modeling" chapter, "Signature declaration" section, of the Practical Alloy book.

https://practicalalloy.github.io/book/chapters/structural-modeling/index.html#signature-declaration
*/

module filesystem

abstract sig Object {}

sig Dir extends Object {}
sig File extends Object {}

one sig Root extends Dir {}

sig Entry {}
sig Name {}

// Show arbitrary instances with the default scope
run example {}
// Show arbitrary instances with scope 4 for top-level signatures
run example {} for 4
// Show arbitrary instances with scope 4 for top-level signatures, 
// but scope 2 for entries and exact scope 3 for names
run example {} for 4 but 2 Entry, exactly 3 Name

run structural_modeling_instance_04 {
  some disj d0, d1, r : Dir {
    Dir  = d0 + d1 + r
    Root = r
    File = none
  }
} expect 1

run structural_modeling_instance_05 {
  some disj d0, r : Dir, disj e0, e1 : Entry, disj n0, n1 : Name {
    Dir   = d0 + r
    Root  = r
    File  = none
    Entry = e0 + e1
    Name  = n0 + n1
  }
} for 4 expect 1