/*  
File system model for the generation of instance 9 of the "Structural modeling"
chapter, "Specifying constraints" section, of the Practical Alloy book.

https://practicalalloy.github.io/book/chapters/structural-modeling/index.html#specifying-constraints
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

fact restrict_object {
  // All objects are directories or files, redundant due to signature declarations
  all x : Object | x in Dir or x in File
}

fact no_shared_entries {
  // Entries cannot be shared between directories
  all e : Entry | lone entries.e
}

fact unique_names {
  // Different entries in the same directory must have different names
  all d : Dir, n : Name | lone (d.entries & name.n)
}

fact no_shared_dirs {
  // A directory cannot be contained in more than one entry
  all d : Dir | lone object.d
}

fact no_dangling_objects {
  // Every object except the root is contained somewhere
  Entry.object = Object - Root
}

run structural_design_instance_09 {
  some disj d0, r, f0, e0, e1, e2, e3, n0, n1, n2 : univ {
    Dir = d0 + r
    Root = r
    File = f0
    Entry = e0 + e1 + e2 + e3
    Name = n0 + n1 + n2
    entries = d0 -> e1 + d0 -> e2 + d0 -> e3
    name = e0 -> n2 + e1 -> n2 + e2 -> n1 + e3 -> n0
    object = e0 -> f0 + e1 -> f0 + e2 -> f0 + e3 -> d0
  }
} for 4
