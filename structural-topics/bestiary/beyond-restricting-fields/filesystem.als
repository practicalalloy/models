/*  
File system model at the end of the "Beyond restricting fields" section, "Arrow
multiplicity constraints" topic, of the Practical Alloy book.

https://practicalalloy.github.io/book/chapters/structural-topics/topics/bestiary/index.html#beyond-restricting-fields
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
  object:>Dir in Entry lone -> Dir
}

fact no_dangling_objects {
  // Every object except the root is contained somewhere
  object in Entry some -> (Object - Root)
}

fact no_shared_entries {
  // Entries cannot be shared between directories (subsumed by one_directory_per_entry)
  entries in Dir lone -> Entry
}

fact one_directory_per_entry {
  // Entries must belong to exactly one a directory
  entries in Dir one -> Entry
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