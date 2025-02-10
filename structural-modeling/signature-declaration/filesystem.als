/*  
File system model at the end of the "Signature declaration" section,
"Structural modeling" chapter, of the Practical Alloy book.

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