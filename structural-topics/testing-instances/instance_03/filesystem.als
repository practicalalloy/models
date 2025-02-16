/*
File system model for the generation of instance 3 of the "Encoding test
instances" topic, "Skolemization and visualization" section, of the Practical
Alloy book.

https://practicalalloy.github.io/book/chapters/structural-topics/topics/testing-instances/index.html#skolemization-and-visualization
*/

module filesystem

abstract sig Object {}

sig Dir extends Object {
  entries : set Entry
}

sig File extends Object {}
one sig F1, F2 extends File {}

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

run test_root_file_dir {
  some disj d0, d1 : Dir, disj f0, f1 : File, disj e0, e1, e2 : Entry, disj n0, n1, n2 : Name {
    Root    = d0
    Dir     = d0 + d1
    File    = f0 + f1
    Entry   = e0 + e1 + e2
    Name    = n0 + n1 + n2
    entries = d0 -> e0 + d0 -> e1 + d1 -> e2
    name    = e0 -> n0 + e1 -> n1 + e2 -> n2
    object  = e0 -> d1 + e1 -> f0 + e2 -> f1
  }
} for 4 Object, 3 Entry, 3 Name

assert no_partitions {
  // Every object is reachable from the root
  all o : Object | reachable[o]
}

// Check that there can be no partitions in a file system within the default scope
check no_partitions
// Check that there can be no partitions in a file system scope 6 for top-level signatures
check no_partitions for 6

run testing_instances_instance_03 {
  some disj r, d1 : Dir, disj f0, f1 : File, disj e0, e1, e2 : Entry, disj n0, n1, n2 : Name {
    Root    = r
    Dir     = r + d1
    File    = f0 + f1
    Entry   = e0 + e1 + e2
    Name    = n0 + n1 + n2
    entries = r -> e0 + r -> e1 + d1 -> e2
    name    = e0 -> n0 + e1 -> n1 + e2 -> n2
    object  = e0 -> d1 + e1 -> f0 + e2 -> f1
  }
} for 4 Object, 3 Entry, 3 Name expect 1