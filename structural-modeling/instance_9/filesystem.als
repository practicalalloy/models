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

fact no_shared_entries {
  // Entries cannot be shared between directories
  all e : Entry | lone entries.e
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

run book_instance9 {
  some disj o0,o1,o2,o3,o4,o5,o6,o7,o8,o9 : univ {
    Dir = o0 + o1
    Root = o1
    File = o2
    Entry = o3 + o4 + o5 + o6
    Name = o7 + o8 + o9
    univ = o0 + o1 + o2 + o3 + o4 + o5 + o6 + o7 + o8 + o9 + Int
    entries = o0 -> o4 + o0 -> o5 + o0 -> o6
    name = o3 -> o9 + o4 -> o9 + o5 -> o8 + o6 -> o7
    object = o3 -> o2 + o4 -> o2 + o5 -> o2 + o6 -> o0
  }
} for 4
