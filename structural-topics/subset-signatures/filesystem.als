module filesystem

sig Tag {}

// Superseded by introduction of tags
// sig Tagged in Object {}

// Superseded by introduction of symbolic links
// sig Tagged in Object {
//    tags : some Tag
// }

abstract sig Object {}

sig Dir extends Object {
    entries : set Entry
}

sig File extends Object {}

one sig Root extends Dir {}

sig Tagged in File + Dir {
	tags : some Tag
}

sig Permission {}

sig BasicObjs = File + Dir {
	permission : one Permission
}

sig Symlink extends Object {}

sig Entry {
    object : one Object,
    name   : one Name
}

sig Name {}

run example {}
run example {
	#Tagged = 2
	one Dir - Root
	Tagged = Root + File
	#Entry = 2
	#Root.entries = 2
	one Root.tags
	#File.tags = 2
	one Symlink
} for 4 but 2 Entry, exactly 3 Name

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

fact entry_one_parent {
    // Entries must belong to exactly one a directory
    all e : Entry | one entries.e
}

fun descendants [o : Object] : set Object {
    o.^(entries.object)
}

fact no_indirect_containment {
    // Directories cannot contain themselves directly or indirectly
    all d : Dir | d not in descendants[d]
}

pred reachable [o : Object] {
    o in Root + descendants[Root]
}

assert no_partitions {
    // Every object is reachable from the root
    all o : Object | reachable[o]
}

check no_partitions
check no_partitions for 6
