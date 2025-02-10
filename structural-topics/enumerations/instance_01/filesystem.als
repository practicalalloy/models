/*  
File system model for the generation of instance 1 of the "Enumeration
signatures" topic, "Field declaration" section, of the Practical Alloy book.

https://practicalalloy.github.io/book/chapters/structural-topics/topics/enumerations/index.html#using-enumeration-signatures
*/

module filesystem

enum Permission { Read, Write, Execute }

abstract sig Object {
  user_permission   : set Permission,
  group_permission  : set Permission,
  others_permission : set Permission
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

// Show arbitrary instances with the default scope
run example {}
// Show arbitrary instances with scope 4 for top-level signatures
run example {} for 4

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

run enumeration_signatures_instance_01 {
  some disj r, f0, e0, n0 : univ {
    Dir = r
    Root = r
    File = f0
    Entry = e0
    Name = n0
    entries = r -> e0
    name = e0 -> n0
    object = e0 -> f0
    user_permission = r -> Read + f0 -> Permission
    group_permission = f0 -> Permission
    others_permission = f0 -> Permission
  }
}
