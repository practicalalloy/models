module filesystem

abstract sig Object {}

sig Dir extends Object {
  entries : set Entry
}

sig File extends Object {}
sig Symlink extends Object {}

one sig Root extends Dir {}

sig Permission {}

sig NonSymlink = Dir + File {
    permission : one Permission
}

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

sig Tagged in Dir + File {
    tags : some Tag
}

sig Entry {
  object : one Object,
  name   : one Name
}

sig Name {}

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

run book_instance4 {
  some disj o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11,o12,o13 : univ {
    Dir = o0
    Root = o0
    File = o1
    Symlink = o2
    Entry = o3 + o4
    Name = o5 + o6
    Tagged = o0 + o1
    Tag = o7 + o8 + o9
    Color = o10
    Text = o11
    Shape = o7 + o8
    Label = o9
    Permission = o12 + o13
    univ = o0 + o1 + o2 + o3 + o4 + o5 + o6 + o7 + o8 + o9 + o10 + o11 + o12 + o13 + Int
    entries = o0 -> o3 + o0 -> o4
    name = o3 -> o5 + o4 -> o6
    object = o3 -> o2 + o4 -> o1
    tags = o0 -> o7 + o1 -> o8 + o1 -> o9
    permission = o0 -> o12 + o1 -> o13
  }
} for 4

