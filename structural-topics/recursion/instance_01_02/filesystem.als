/*  
File system model for the generation of instances 1 and 2 of the "Handling
recursion" topic, "Recursive Alloy functions" section, of the Practical Alloy
book.

https://practicalalloy.github.io/book/chapters/structural-topics/topics/recursion/index.html#recursive-alloy-functions
*/

module filesystem

open util/natural

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

fun depth [o: Object] : Natural {
  o in Root implies Zero
  else inc[max[{n : Natural | some x : entries.object.o | n = depth[x]}]]
}

// needs recursion depth of 2 set in options
run depth2 {
  some f : File | depth[f] = inc[One]
} for 5 but 3 Name

// needs recursion depth of 3 set in options
run depth3 {
  some f : File | depth[f] = inc[inc[One]]
} for 5 but 3 Name

assert no_partitions {
  // Every object is reachable from the root
  all o : Object | reachable[o]
}

// Check that there can be no partitions in a file system within the default scope
check no_partitions
// Check that there can be no partitions in a file system scope 6 for top-level signatures
check no_partitions for 6

// needs recursion depth of 2 set in options
run recursion_instance_01 {
  some f : File | depth[f] = inc[One]
  some disj d1, d2 : Dir, f0 : File, disj e1, e2, e3 : Entry, disj n1, n2, n3 : Name {
    Root    = d1
    Dir     = d1 + d2
    File    = f0
    Entry   = e1 + e2 + e3
    Name    = n1 + n2 + n3
    entries = d1 -> e1 + d1 -> e2 + d2 -> e3
    name    = e1 -> n1 + e2 -> n2 + e3 -> n3
    object  = e1 -> d2 + e2 -> f0 + e3 -> f0
  }
} for 5 but 3 Name expect 1

// needs recursion depth of 3 set in options
run recursion_instance_02 {
  some f : File | depth[f] = inc[inc[One]]
  some disj d0, d1, r : Dir, f0 : File, disj e0, e1, e2, e3 : Entry, disj n0, n1, n2 : Name {
    Root    = r
    Dir     = d0 + d1 + r
    File    = f0
    Entry   = e0 + e1 + e2 + e3
    Name    = n0 + n1 + n2
    entries = r -> e3 + d1 -> e1 + d1 -> e0 + d0 -> e2
    name    = e0 -> n2 + e1 -> n1 + e2 -> n2 + e3 -> n0
    object  = e0 -> f0 + e1 -> d0 + e2 -> f0 + e3 -> d1
  }
} for 5 but 3 Name expect 1