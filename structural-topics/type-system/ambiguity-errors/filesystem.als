module filesystem

abstract sig Object {}

sig Dir extends Object {
  contents : set Entry
}

sig File extends Object {}

one sig Root extends Dir {}

sig Entry {
  contents : one Object,
  name     : one Name
}

sig Name {}

run example {}
run example {} for 4
run example {} for 4 but 2 Entry, exactly 3 Name

fact unique_names {
  // Different entries in the same directory must have different names
  all d : Dir, n : Name | lone (d.contents & name.n)
}

fact no_shared_dirs {
  // A directory cannot be contained in more than one entry
  all d : Dir | lone contents.d
}

fact no_dangling_objects {
  // Every object except the root is contained somewhere
  Entry.contents = Object - Root
}

fact one_directory_per_entry {
  // Entries must belong to exactly one a directory
  all e : Entry | one contents.e
}

fun descendants [o : Object] : set Object {
  o.^(contents.contents)
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

fact no_indirect_containment {
   // Directories cannot descend from themselves
   all d : Dir | d not in descendants[d]
}

check no_partitions
check no_partitions for 6

run not_ambiguous { some Root.contents }
run ambiguous { some contents }
