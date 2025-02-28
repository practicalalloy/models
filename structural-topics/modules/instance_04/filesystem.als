/*  
File system model for the generation of instance 4 of the "Module system" topic,
"Private declarations" section, of the Practical Alloy book.

https://practicalalloy.github.io/chapters/structural-topics/topics/modules/index.html#private-declarations
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
  rootedAt[entries.object, Root]
}

fact time {
  all d : Dir | d.entries.object.time in d.time.*next
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

run modules_instance_04 {
  some disj d0, d1 : Dir, f0 : File, disj e0, e1 : Entry, disj n0, n1 : Name{
    Dir     = d0 + d1
    Root    = d1
    File    = f0
    Entry   = e0 + e1
    Name    = n0 + n1
    entries = d1->e0 + d1->e1
    name    = e0->n0 + e1->n1
    object  = e0->f0 + e1->d0
    time    in d0->last + d1->first + f0->last
  }
} expect 1