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

run example {}
run example {} for 4
run example {} for 4 but 2 Entry, exactly 3 Name

fact restrict_object {
    // All objects are directories or files, redundant due to signature declarations
    Object in Dir + File

    // Alternative formulation
    // all x : Object | x in Dir or x in File
}

// Superseded by fact entry_one_parent
// fact entry_at_most_parent {
//     // Entries cannot be shared between directories
//     all x, y : Dir | x != y implies no (x.entries & y.entries)
// 
//     // Alternative formulation
//     // all disj x, y : Dir | no (x.entries & y.entries)
// 
//     // Alternative formulation
//     // all e : Entry | lone entries.e
// }

fact unique_names {
    // Different entries in the same directory must have different names
    all d : Dir, disj x, y : d.entries | x.name != y.name

    // Alternative formulation
    // all d : Dir, n : Name | lone (d.entries & name.n)
}

fact no_shared_dirs {
    // A directory cannot be contained in more than one entry
    all d : Dir | lone object.d
}

fact no_dangling_objects {
    // Every object except the root is contained somewhere
    Entry.object = Object - Root
}

fact entry_one_parent {
    // Entries must belong to exactly one a directory
    all e : Entry | one entries.e
}

// Superseded by fact no_indirect_containment
// fact no_self_containment {
//     // Directories cannot contain themselves
//     all d : Dir | d not in d.entries.object
// }

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

