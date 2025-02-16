/*  
File system model for the generation of instances 1 and 2 of the "Model finding"
topic, "Skolemization" section, of the Practical Alloy book.

https://practicalalloy.github.io/book/chapters/structural-topics/topics/analysis/index.html#skolemization
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

run all_entries_dir {
  Entry.object in Dir
} for 2

run some_entries_dir {
  some d : Dir | d in Entry.object
} for 2

check all_entries_same_name {
  all s : set Entry | lone s.name
}

assert no_partitions {
  // Every object is reachable from the root
  all o : Object | reachable[o]
}

// Check that there can be no partitions in a file system within the default scope
check no_partitions
// Check that there can be no partitions in a file system scope 6 for top-level signatures
check no_partitions for 6

run model_finding_instance_01 {
  Entry.object in Dir
  some disj r, d0 : Dir, e0 : Entry, n0 : Name {
    Dir     = r + d0
    Root    = r
    File    = none
    Entry   = e0
    Name    = n0
    entries = r -> e0
    name    = e0 -> n0
    object  = e0 -> d0
  }
} for 3 expect 1

check model_finding_instance_02 {
  (some disj r, d0 : Dir, f0 : File, disj e0, e1, e2 : Entry, disj n0, n1, n2 : Name {
    Dir     = r + d0
    Root    = r
    File    = f0
    Entry   = e0 + e1 + e2
    Name    = n0 + n1 + n2
    entries = r -> e0 + d0 -> e1 + d0 -> e2
    name    = e0 -> n2 + e1 -> n1 + e2 -> n0
    object  = e0 -> d0 + e1 -> f0 + e2 -> f0
  }) implies all s : set Entry | lone s.name
} for 3 expect 1
