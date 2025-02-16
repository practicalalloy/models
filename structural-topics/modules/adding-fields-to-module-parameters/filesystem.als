/*  
File system model at the end of the "Adding fields to module parameters"
section, "Module system" topic, of the Practical Alloy book.

https://practicalalloy.github.io/book/chapters/structural-topics/topics/modules/index.html#adding-fields-to-module-parameters
*/

module filesystem
open graph[Object] 
open timestamp[Object, Timestamp]

sig Timestamp {}

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

fact rooted_dag {
  dag[entries.object]
  rootedAt[entries.object,Root]
}

fact time {
  all d : Dir | d.entries.object.(TimeAux.aux_time) in d.(TimeAux.aux_time).*next
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