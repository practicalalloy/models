/*  
Model for the generation of instance 10 of the "Structural modeling"
chapter, "Verifying assertions" section, of the Practical Alloy book.

https://practicalalloy.github.io/book/chapters/structural-modeling/index.html#verifying-assertions
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

fact one_directory_per_entry {
  // Entries must belong to exactly one a directory
  all e : Entry | one entries.e
}

fact no_self_containment {
  // Directories cannot contain themselves
  all d : Dir | d not in d.entries.object
}

fun descendants [o : Object] : set Object {
  o.^(entries.object)
}

pred reachable [o : Object] {
  o in Root + descendants[Root]
}

// Show arbitrary instances with the default scope
run example {}
// Show arbitrary instances with scope 4 for top-level signatures
run example {} for 4

assert no_partitions {
  // Every object is reachable from the root
  all o : Object | reachable[o]
}

// Check that there can be no partitions in a file system within the default scope
check no_partitions

check structural_design_instance_10 {
  some disj d0, d1, r, e0, e1, n0 : univ {
    Dir = d0 + d1 + r
    Root = r
    File = none
    Entry = e0 + e1
    Name = n0
    entries = d0 -> e0 + d1 -> e1
    name = e0 -> n0 + e1 -> n0
    object = e0 -> d1 + e1 -> d0
  } implies all o : Object | reachable[o]
} for 3 expect 1
