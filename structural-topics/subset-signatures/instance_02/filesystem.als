/*  
File system model for the generation of instance 2 of the "Subset signatures"
topic, "Mixing subset and extension signatures" section, of the Practical
Alloy book.

https://practicalalloy.github.io/book/chapters/structural-topics/topics/subset-signatures/index.html#mixing-subset-and-extension-signatures
*/

module filesystem

abstract sig Object {}

sig Dir extends Object {
  entries : set Entry
}

sig File extends Object {}

one sig Root extends Dir {}

sig Tag {}

sig Tagged in Object {
    tags : some Tag
}

sig Entry {
  object : one Object,
  name   : one Name
}

sig Name {}

// Show arbitrary instances with the default scope
run example {}
// Show arbitrary instances with scope 4 for top-level signatures
run example {} for 4

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

assert no_partitions {
  // Every object is reachable from the root
  all o : Object | reachable[o]
}

check no_partitions
check no_partitions for 6

run subset_signatures_instance_02 {
  some disj d0, r, f0, e0, e1, n0, n1, n2, t0, t1, t2 : univ {
    Dir = d0 + r
    Root = r
    File = f0
    Entry = e0 + e1
    Name = n0 + n1 + n2
    Tagged = r + f0
    Tag = t0 + t1 + t2
    entries = r -> e0 + r -> e1
    name = e0 -> n1 + e1 -> n2
    object = e0 -> f0 + e1 -> d0
    tags = r -> t2 + f0 -> t0 + f0 -> t1
  }
} for 4
