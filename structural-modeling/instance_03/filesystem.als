/*  
File system model for the generation of instance 3 of the "Structural modeling"
chapter, "Signature declaration" section, of the Practical Alloy book.

https://practicalalloy.github.io/chapters/structural-modeling/index.html#signature-declaration
*/

module filesystem

sig Object {}

sig Dir extends Object {}
sig File extends Object {}

// Show arbitrary instances with the default scope
run example {}

run structural_modeling_instance_03 {
  some disj f0, d0, o0 : Object {
    Object = o0 + f0 + d0
    Dir    = d0
    File   = f0
  }
} expect 1