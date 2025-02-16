/*  
File system model for the generation of instance 1 of the "Working with
integers" topic, "Models with integers" section, of the Practical Alloy book.

https://practicalalloy.github.io/book/chapters/structural-topics/topics/integers/index.html#models-with-integers
*/

module filesystem

one sig Capacity in Int {}

abstract sig Object {}

sig Dir extends Object {
  entries : set Entry
}

sig File extends Object {
  size : one Int
}

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

fun descendants [o : Object] : set Object {
  o.^(entries.object)
}

pred reachable [o : Object] {
  o in Root + descendants[Root]
}

fact no_indirect_containment {
  // Directories cannot descend from themselves
  all d : Dir | d not in descendants[d]
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
// Check that there can be no partitions in a file system scope 6 for top-level signatures
check no_partitions for 6

run integers_instance_01 {
  some disj r : Dir, disj f0, f1, f2 : File, 
       disj e0, e1, e2 : Entry, disj n0, n1, n2 : Name {
    Root     = r
    Dir      = r
    File     = f0 + f1 + f2
    Entry    = e0 + e1 + e2
    Name     = n0 + n1 + n2
    Capacity = 4
    entries  = r -> e0 + r -> e1 + r -> e2
    name     = e0 -> n2 + e1 -> n1 + e2 -> n0
    object   = e0 -> f1 + e1 -> f2 + e2 -> f0
    size     = f0 -> 6 + f1 -> 1 + f2 -> 5
  }
} for 4 expect 1