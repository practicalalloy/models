/*  
File system model for the generation of instance 2 of the "Enumeration
signatures" topic, "An alternative encoding" section, of the Practical Alloy
book.

https://practicalalloy.github.io/book/chapters/structural-topics/topics/enumerations/index.html#an-alternative-encoding
*/

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

// Show arbitrary instances with the default scope
run example {}
// Show arbitrary instances with scope 4 for top-level signatures
run example {} for 4

run distinct_permissions { 
  some disj o1, o2 : Object | o1.mode != o2.mode
} for 4

assert no_partitions {
  // Every object is reachable from the root
  all o : Object | reachable[o]
}

// Check that there can be no partitions in a file system within the default scope
check no_partitions
// Check that there can be no partitions in a file system scope 6 for top-level signatures
check no_partitions for 6

run enumerations_instance_02 {
  some disj o1, o2 : Object | o1.mode != o2.mode
  some r : Dir, f0 : File, e0 : Entry, n0 : Name, 
       disj p0, p1, p2, p3 : PermissionAssignment {
    Dir                  = r
    Root                 = r
    File                 = f0
    Entry                = e0
    Name                 = n0
    PermissionAssignment = p0 + p1 + p2 + p3
    entries              = r -> e0
    name                 = e0 -> n0
    object               = e0 -> f0
    mode                 = r -> p0 + r -> p1 + r -> p2 + f0 -> p0 + f0 -> p1 + f0 -> p3
    class                = p2 -> User + p0 -> Other + p1 -> Group + p3 -> User
    permission           = p2 -> Read + p1 -> Read + p3 -> Execute + p3 -> Read 
  }
} for 4 expect 1