/*  
File system model for the generation of instance 3 of the "Subset signatures"
topic, "Simulating multiple inheritance" section, of the Practical Alloy book.

https://practicalalloy.github.io/book/chapters/structural-topics/topics/subset-signatures/index.html#simulating-multiple-inheritance
*/

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

run subset_signatures_instance_03 {
  some disj r, t0, t1, t2, c0, x0 : univ {
    Dir = r
    Root = r
    File = none
    Entry = none
    Name = none
    Tagged = none
    Tag = t0 + t1 + t2
    Color = c0
    Text = x0
    Shape = t0 + t2
    Label = t1 + t2
    entries = none -> none
    name = none -> none
    object = none -> none
    tags = none -> none
  }
} for 4

