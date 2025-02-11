/*   
File system model at the end of the "Controlling scopes" section,
"Commands in detail" topic, of the Practical Alloy book.

https://practicalalloy.github.io/book/chapters/structural-topics/topics/commands/index.html#controlling-scopes
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

// Check whether every object is reachable from the root
check no_partitions {
  all o : Object | reachable[o]
} for 6

pred depth2 {
  // There are some objects at depth 2 of the file system
  some Root.entries.object.entries.object
}

// Show instances with at least depth 2 without files
run depth2 for 4 but 0 File
// Show instances with at least depth 2 without at most 1 file
run depth2 for 4 but 1 File
// Show instances with at least depth 2 without at most 2 files
run depth2 for 4 but 2 File

pred empty_dir [d : Dir] {
  // Tests whether directory d is empty
  no d.entries
}

// Show instances where there is some empty directory
run empty_dir for 3

// Show arbitrary instances with overall scope of 3 for top-level signatures
run scope_3 {} for 3
// Show arbitrary instances with overall scope of 3, but at most 2 names
run names_2 {} for 3 but 2 Name
// Show arbitrary instances with overall scope of 3, but at most 3 directories and 3 files
// Will result in 6 objects even though it is a top-level signature
run files_3_dirs_3 {} for 3 but 3 Dir, 3 File
// Show instances with some files with overall scope of 3, but at most 3 directories
// Is unsatisfiable since there is no scope left for files
run dirs_3 { some File } for 3 but 3 Dir
