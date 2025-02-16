/*  
File system model at the end of the "Dealing with integer overflows" section,
"Working with integers" topic, of the Practical Alloy book.

https://practicalalloy.github.io/book/chapters/structural-topics/topics/integers/index.html#dealing-with-integer-overflows
*/

module filesystem

one sig Capacity in Int {}

abstract sig Object {}

sig Dir extends Object {
  entries : set Entry
}

sig File extends Object {
  size : one Int
}

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

fact positive_sizes {
  // All file sizes are positive
  all f : File | gt[f.size, 0]
}

fact below_capactiy {
  // The sum of the size of all files cannot exceed the capacity
  (sum f : File | f.size) <= Capacity
}

fact size_limits {
  // Guarantee file sizes do not overflow
  all f : File | f.size <= div[max, #File]
}

// Show arbitrary instances with the default scope
run example {}
// Show arbitrary instances with scope 4 for top-level signatures
run example {} for 4

run full_root { 
  #(Root.entries) = 3 } 
for 4

// Execute with prevent overflows
check big_files {
  all f:File | f.size > 10
}

assert no_partitions {
  // Every object is reachable from the root
  all o : Object | reachable[o]
}

// Check that there can be no partitions in a file system within the default scope
check no_partitions
// Check that there can be no partitions in a file system scope 6 for top-level signatures
check no_partitions for 6