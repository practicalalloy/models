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

run example {} expect 1
run example {} for 4 expect 1
run example {} for 4 but 2 Entry, exactly 3 Name expect 1

run book_instance_3 {
  some disj d0, d1, d2 : Dir, f : File, disj n0, n1, n2 : Name, disj e0, e1, e2 : Entry {
    File = f
    Root = d2
    Dir = d0 + d1 + d2
    Entry = e0 + e1 + e2
    Name = n0 + n1 + n2
    name = e0 -> n1 + e1 -> n0 + e2 -> n2
    object = e0 -> d0 + e1 -> d1 + e2 -> f
    entries = d2 -> e1 + d2 -> e2 + d1 -> e0
  }
} for 4 expect 1

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

