module filesystem

abstract sig Object {}

sig Dir extends Object {
  entries : set Entry
}

sig File extends Object {}

one sig Root extends Dir {}

sig Tag {}

sig Color, Text {}

sig Shape in Tag {
  color : one Color
}

sig Label in Tag {
  text : one Text
}

sig Alert in Tag {}

fact tag_hierarchy {
  // Tag is abstract
  Tag = Shape + Label
  // Alerts are labeled shapes
  Alert = Shape & Label
}

sig Tagged in Object {
    tags : some Tag
}

sig Entry {
  object : one Object,
  name   : one Name
}

sig Name {}

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

run book_instance3 {
  some disj o0,o1,o2,o3,o4,o5 : univ {
    Dir = o0
    Root = o0
    File = none
    Entry = none
    Name = none
    Tagged = none
    Tag = o1 + o2 + o3
    Color = o4
    Text = o5
    Shape = o1 + o3
    Label = o2 + o3
    univ = o0 + o1 + o2 + o3 + o4 + o5 + Int
    entries = none -> none
    name = none -> none
    object = none -> none
    tags = none -> none
  }
} for 4

