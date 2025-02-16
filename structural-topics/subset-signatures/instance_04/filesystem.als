/*  
File system model for the generation of instance 4 of the "Subset signatures"
topic, "Cross-signature subsets" section, of the Practical Alloy book.

https://practicalalloy.github.io/book/chapters/structural-topics/topics/subset-signatures/index.html#cross-signature-subsets
*/

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

sig Tagged in Dir + File {
  tags : some Tag
}

sig Entry {
  object : one Object,
  name   : one Name
}

sig Name {}

fact tag_hierarchy {
  // Tag is abstract
  Tag = Shape + Label
  // Alerts are labeled shapes
  Alert = Shape & Label
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

assert no_partitions {
  // Every object is reachable from the root
  all o : Object | reachable[o]
}

// Check that there can be no partitions in a file system within the default scope
check no_partitions
// Check that there can be no partitions in a file system scope 6 for top-level signatures
check no_partitions for 6

run subset_signatures_instance_04 {
  some r : Dir, f0 : File, s0 : Symlink, disj e0, e1 : Entry, disj n0, n1 : Name, 
       disj t0, t1, t2 : Tag, c0 : Color, x0 : Text, disj p0, p1 : Permission {
    Dir        = r
    Root       = r
    File       = f0
    Symlink    = s0
    Entry      = e0 + e1
    Name       = n0 + n1
    Tagged     = r + f0
    Tag        = t0 + t1 + t2
    Color      = c0
    Text       = x0
    Shape      = t0 + t1
    Label      = t2
    Permission = p0 + p1
    entries    = r -> e0 + r -> e1
    name       = e0 -> n0 + e1 -> n1
    object     = e0 -> s0 + e1 -> f0
    tags       = r -> t0 + f0 -> t1 + f0 -> t2
    permission = r -> p0 + f0 -> p1
  }
} for 4