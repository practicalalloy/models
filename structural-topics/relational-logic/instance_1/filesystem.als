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

run example {}
run example {} for 4
run example {} for 4 but 2 Entry, exactly 3 Name

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

// Check that there can be no partitions in a file system within the default scope
check no_partitions
// Check that there can be no partitions in a file system scope 6 for top-level signatures
check no_partitions for 6

run book_instance1 {
  some disj o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10 : univ {
    Dir = o0 + o1 + o2
    Root = o2
    File = o3
    Entry = o4 + o5 + o6 + o7
    Name = o8 + o9 + o10
    univ = Object + Name + Entry + Int
    entries = o2 -> o4 + o2 -> o5 + o2 -> o6 + o0 -> o7
    name = o4 -> o8 + o5 -> o10 + o6 -> o9 + o7 -> o9
    object = o4 -> o3 + o5 -> o3 + o6 -> o0 + o7 -> o1
  }
} for 4
