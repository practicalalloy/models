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

pred no_self_containment {
   // Directories cannot contain themselves
   all d : Dir | d not in d.entries.object
}

pred no_indirect_containment {
  // Directories cannot contain themselves directly or indirectly
  all d : Dir | d not in descendants[d]
}

pred no_partitions {
  // Every object is reachable from the root
  all o : Object | reachable[o]
}

check bad_containment {
  no_self_containment implies no_partitions
} for 6 expect 1

check good_containment {
  no_indirect_containment implies no_partitions
} for 6 expect 0

pred depth2 {
    some Root.entries.object.entries.object
}

run depth2 for 4 but 0 File
run depth2 for 4 but 1 File
run depth2 for 4 but 2 File

pred empty_dir [d: Dir] {
    no d.entries
}

run empty_dir for 3

run scope_3 {} for 3
run names_2 {} for 3 but 2 Name
run files_3_dirs_3 {} for 3 but 3 Dir, 3 File
run dirs_3 { some File } for 3 but 3 Dir
run no_overall {} for 3 Object, 2 Name, 2 Entry
run files_exact2 {} for 3 but exactly 2 File
