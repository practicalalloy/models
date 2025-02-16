/*  
File system model for the generation of instance 1 of the "A relational logic
primer" topic of the Practical Alloy book.

https://practicalalloy.github.io/chapters/structural-topics/topics/relational-logic/index.html#a-relational-logic-primer
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

run relational_logic_instance_01 {
  some disj d0, d1, r : Dir, f0 : File, disj e0, e1, e2, e3 : Entry, disj n0, n1, n2 : Name {
    Dir     = d0 + d1 + r
    Root    = r
    File    = f0
    Entry   = e0 + e1 + e2 + e3
    Name    = n0 + n1 + n2
    entries = r -> e0 + r -> e1 + r -> e2 + d0 -> e3
    name    = e0 -> n0 + e1 -> n2 + e2 -> n1 + e3 -> n1
    object  = e0 -> f0 + e1 -> f0 + e2 -> d0 + e3 -> d1
  }
} for 4 expect 1