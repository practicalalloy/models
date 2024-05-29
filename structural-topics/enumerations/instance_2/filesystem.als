module filesystem

enum Permission { Read, Write, Execute }

enum Class { User, Group, Other }

sig PermissionAssignment {
  permission : set Permission,
  class      : one Class
}

abstract sig Object {
  mode : set PermissionAssignment
}

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

run distinct_permissions { 
  some disj o1,o2:Object | o1.mode != o2.mode
} for 4

fact all_classes_assigned {
  // There is one permission assigned to each group
  all o : Object, c : Class | one o.mode & class.c
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

run distinct_permissions {
  some disj o0, o1, o2, o3, o4, o5, o6, o7 : univ {
    Dir = o0
    Root = o0
    File = o1
    Entry = o2
    Name = o3
    PermissionAssignment = o4 + o5 + o6 + o7
--    univ = o0 + o1 + o2 + o3 + o4 + o5 + o6 + o7 + Permission + Class + Int
    entries = o0 -> o2
    name = o2 -> o3
    object = o2 -> o1
    mode = o0 -> o4 + o0 -> o5 + o0 -> o6 + o1 -> o4 + o1 -> o5 + o1 -> o7
    class = o6 -> User + o4 -> Other + o5 -> Group + o7 -> User
    permission = o6 -> Read + o5 -> Read + o7 -> Execute + o7 -> Read 
  }
} for 4
