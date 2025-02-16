/*   
File system model for the generation of instances 1 and 2 of the "Structural
modeling" chapter, "Signature declaration" section, of the Practical Alloy book.

https://practicalalloy.github.io/book/chapters/structural-modeling/index.html#signature-declaration
*/

module filesystem

sig Object {}

sig Dir in Object {}
sig File in Object {}

// Show arbitrary instances with the default scope
run example {}

run structural_modeling_instance_01 {
  some o0, o1 : Object {
    Object = o0 + o1
    Dir    = o1
    File   = o0
  }
} expect 1

run structural_modeling_instance_02 {
  some o0 : Object {
    Object = o0
    Dir    = o0
    File   = o0
  }
} expect 1