/*  
File system model for the generation of instances 3 and 4 of the "Handling
recursion" topic, "Recursion through memoization" section, of the Practical
Alloy book.

https://practicalalloy.github.io/chapters/structural-topics/topics/recursion/index.html#recursion-through-memoization
*/

module filesystem

open util/natural

abstract sig Object {
  depth : one Natural
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

fact calculate_depth {
  all o : Object |
    o in Root implies o.depth = Zero
    else o.depth = inc[max[(entries.object.o).depth]]
}

// Show arbitrary instances with the default scope
run example {}
// Show arbitrary instances with scope 4 for top-level signatures
run example {} for 4

run depth2 {
  some f : File | f.depth = inc[One]
} for 5 but 3 Name

run depth4 {
  some f : File | f.depth = inc[inc[inc[One]]]
} for 5 but 3 Name

assert no_partitions {
  // Every object is reachable from the root
  all o : Object | reachable[o]
}

// Check that there can be no partitions in a file system within the default scope
check no_partitions
// Check that there can be no partitions in a file system scope 6 for top-level signatures
check no_partitions for 6

run recursion_instance_03 {
  some f : File | f.depth = inc[One]
  some disj d0, d1, r : Dir, disj f0, f1 : File, disj e0, e1, e2, e3, e4 : Entry, disj n0, n1, n2 : Name {
    Root    = r
    Dir     = r + d0 + d1
    File    = f0 + f1
    Entry   = e0 + e1 + e2 + e3 + e4
    Name    = n0 + n1 + n2
    entries = r->e3 + r->e4 + d1->e0 + d1->e1 + d1->e2
    name    = e0->n2 + e1->n1 + e2->n0 + e3->n2 + e4->n1
    object  = e0->f0 + e1->f0 + e2->f1 + e3->d0 + e4->d1
  }
} for 5 but 3 Name expect 1

run recursion_instance_04 {
  some f : File | f.depth = inc[inc[inc[One]]]
  some disj d0, d1, d2, r : Dir, f0 : File, disj e0, e1, e2, e3, e4 : Entry, disj n0, n1, n2 : Name {
    Root    = r
    Dir     = r + d0 + d1 + d2
    File    = f0
    Entry   = e0 + e1 + e2 + e3 + e4
    Name    = n0 + n1 + n2
    entries = r->e3 + r->e4 + d0->e2 + d1->e1 + d2->e0
    name    = e0->n2 + e1->n2 + e2->n2 + e3->n1 + e4->n0
    object  = e0->f0 + e1->d2 + e2->d1 + e3->f0 + e4->d0
  }
} for 5 but 3 Name expect 1