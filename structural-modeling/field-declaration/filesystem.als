/*  
File system model at the end of the "Field declaration" section,
"Structural modeling" chapter, of the Practical Alloy book.

https://practicalalloy.github.io/chapters/structural-modeling/index.html#field-declaration
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