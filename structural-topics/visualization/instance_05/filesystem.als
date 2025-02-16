/*  
File system model for the generation of instance 5 of the "Visualization
customization" topic, "Improving visualizations with derived relations" section,
of the Practical Alloy book.

https://practicalalloy.github.io/book/chapters/structural-topics/topics/themes/index.html#improving-visualizations-with-derived-relations
*/

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

fun empty_dirs : set Dir {
  Dir - entries.Entry
}

// Show arbitrary instances with the default scope
run example {}
// Show arbitrary instances with scope 4 for top-level signatures
run example {} for 4

run visualization_instance_05 {
  some disj d0, d1, r : Dir, f0 : File, disj n0, n1, n2 : Name, disj e0, e1, e2 : Entry {
    File    = f0
    Root    = r
    Dir     = d0 + d1 + r
    Entry   = e0 + e1 + e2
    Name    = n0 + n1 + n2
    name    = e0 -> n1 + e1 -> n0 + e2 -> n2
    object  = e0 -> d0 + e1 -> d1 + e2 -> f0
    entries = r -> e1 + r -> e2 + d1 -> e0
  }
} for 4 expect 1