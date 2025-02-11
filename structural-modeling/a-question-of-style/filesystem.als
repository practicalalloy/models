/*  
File system model at the end of the "A question of style" section,
"Structural modeling" chapter, of the Practical Alloy book.

https://practicalalloy.github.io/book/chapters/structural-modeling/index.html#a-question-of-style
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

// Navigational style
fact no_shared_dirs {
  // A directory cannot be contained in more than one entry
  all d : Dir | lone object.d
}

// Pointwise style
fact no_shared_entries {
  // Entries cannot be shared between directories
  all x, y : Dir, e : Entry | x->e in entries and y->e in entries implies x = y
}

// Relational style
fact no_shared_entries {
  // Entries cannot be shared between directories
  all x, y : Dir | x != y implies no (x.entries & y.entries)
}

// Pointfree style
fact no_shared_entries {
  // Entries cannot be shared between directories
  entries.~entries in iden
}

fact no_dangling_objects {
  // Every object except the root is contained somewhere
  Entry.object = Object - Root
}

fact one_directory_per_entry {
  // Entries must belong to exactly one a directory
  all e : Entry | one entries.e
}

fact no_self_containment {
  // Directories cannot contain themselves
  all d : Dir | d not in d.entries.object
}

// Show arbitrary instances with the default scope
run example {}
// Show arbitrary instances with scope 4 for top-level signatures
run example {} for 4
