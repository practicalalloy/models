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

fact no_self_containment {
  // Directories cannot contain themselves
  all d : Dir | d not in d.entries.object
}

fun descendants [o : Object] : set Object {
  o.^(entries.object)
}

pred reachable [o : Object] {
  o in Root + descendants[Root]
}

assert no_partitions {
  // Every object is reachable from the root
  all o : Object | reachable[o]
}

check no_partitions

run book_instance_1 {
  some disj o0,o1,o2,o3,o4,o5,o6,o7 : univ {
    Dir = o0 + o1
    Root = o1
    File = o2
    Entry = o3 + o4 + o5
    Name = o6 + o7
    univ = o0 + o1 + o2 + o3 + o4 + o5 + o6 + o7 + Int
    entries = o0 -> o3 + o1 -> o4 + o1 -> o5
    name = o3 -> o6 + o4 -> o7 + o5 -> o6
    object = o3 -> o2 + o4 -> o2 + o5 -> o0
  }
}
