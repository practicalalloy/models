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

--run example {}
--run example {} for 4 but 2 Entry, exactly 3 Name

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

fact entry_one_parent {
    // Entries must belong to exactly one a directory
    all e : Entry | one entries.e
}

fun descendants [o : Object] : set Object {
    o.^(entries.object)
}

fact no_indirect_containment {
    // Directories cannot contain themselves directly or indirectly
    all d : Dir | d not in descendants[d]
}

pred reachable [o : Object] {
    o in Root + descendants[Root]
}

assert no_partitions {
    // Every object is reachable from the root
    all o : Object | reachable[o]
}

--check no_partitions
--check no_partitions for 6

pred root_file_dir [d1,d2: Dir, f1, f2: File, e1, e2, e3: Entry] {
    Root  = d1
    Dir   = d1 + d2
    File  = f1 + f2
    Entry = e1 + e2 + e3
    entries = d1 -> e1 + d1 -> e2 + d2 -> e3
    object  = e1 -> d2 + e2 -> f1 + e3 -> f2
}


run test_root_file_dir {
  some disj d1, d2 : Dir, disj f1, f2 : File, disj e1, e2, e3 : Entry, disj n1, n2, n3 : Name { 
	root_file_dir[d1,d2,f1,f2,e1,e2,e3]
    Name  = n1 + n2 + n3
    name    = e1 -> n1 + e2 -> n2 + e3 -> n3
  }
} for 4 Object, 3 Entry, 3 Name expect 1

run test_root_file_dir_bad_name {
    some disj d1, d2 : Dir, disj f1, f2 : File, disj e1, e2, e3 : Entry, disj n1, n3 : Name { 
      root_file_dir[d1,d2,f1,f2,e1,e2,e3]
      Name  = n1 + n3
      name    = e1 -> n1 + e2 -> n1 + e3 -> n3
    }
} for 4 Object, 3 Entry, 2 Name expect 0

run test_root_file_dir_same_name {
  some disj d1, d2 : Dir, disj f1, f2 : File, disj e1, e2, e3 : Entry, disj n1, n2 : Name { 
	root_file_dir[d1,d2,f1,f2,e1,e2,e3]
    Name  = n1 + n2
    name    = e1 -> n1 + e2 -> n2 + e3 -> n2
  }
} for 4 Object, 3 Entry, 2 Name expect 1

/* without disj
run bad_test_root_2_files {
  some d1 : Dir, f1, f2 : File, e1, e2 : Entry, n1, n2 : Name { 
    Root  = d1
    Dir   = d1
    File  = f1 + f2
    Entry = e1 + e2
    Name  = n1 + n2
    entries = d1 -> e1 + d1 -> e2
    name    = e1 -> n1 + e2 -> n2
    object  = e1 -> f1 + e2 -> f2
  }
} for 3
*/
