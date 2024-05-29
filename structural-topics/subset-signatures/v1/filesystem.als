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

run example {}
run example {} for 4
run example {} for 4 but 2 Entry, exactly 3 Name

fact restrict_object {
  // All objects are directories or files, redundant due to signature declarations
  all x : Object | x in Dir or x in File
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

fact no_indirect_containment {
   // Directories cannot descend from themselves
   all d : Dir | d not in descendants[d]
}

check no_partitions
check no_partitions for 6

run book_instance2 {
  some disj o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10 : univ {
    Dir = o0 + o1
    Root = o1
    File = o2
    Entry = o3 + o4
    Name = o5 + o6 + o7
    Tagged = o1 + o2
    Tag = o8 + o9 + o10
    univ = o0 + o1 + o2 + o3 + o4 + o5 + o6 + o7 + o8 + o9 + o10 + Int
    entries = o1 -> o3 + o1 -> o4
    name = o3 -> o6 + o4 -> o7
    object = o3 -> o2 + o4 -> o0
    tags = o1 -> o10 + o2 -> o8 + o2 -> o9
  }
} for 4 but 2 Entry, exactly 3 Name
