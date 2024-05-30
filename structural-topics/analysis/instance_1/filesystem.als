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

run all_entries_dir {
  Entry.object in Dir
} for 2

run some_entries_dir {
  some d: Dir | d in Entry.object
} for 2

check all_entries_same_name {
  all s : set Entry | lone s.name
}

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

run book_instance1 {
  some disj o0, o1, o2, o3 : univ {
    Dir = o0 + o1
    Root = o0
    File = none
    Entry = o2
    Name = o3
    univ = o0 + o1 + o2 + o3 + Int
    entries = o0 -> o2
    name = o2 -> o3
    object = o2 -> o1
  }
} for 3
