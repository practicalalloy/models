open util/natural

module filesystem

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

fact {
	all o:Object | 
		o in Root implies o.depth = Zero else o.depth = inc[max[entries.object.o.depth]]
}

/* 
// Recursive version
fun depth [o:Object] : Natural {
	o in Root implies Zero
	else inc[max[{n : Natural | some x: entries.object.o | n = depth[x]}]]
}
*/
run depth2 {
	some f:File | f.depth = inc[One]
--	some f:File | depth[f] = inc[One] // Recursive version
} for 5 but 3 Name

run depth3 {
	some f:File | f.depth = inc[inc[One]] 
--	some f:File | depth[f] = inc[inc[One]] // Recursive version
} for 5 but 3 Name


run depth4 {
	some f:File | f.depth = inc[inc[inc[One]]]
} for 5 but 3 Name


run depth5 {
	some f:File | depth[f] = inc[inc[inc[inc[One]]]]

} for 8 but 3 Name, 5 Natural



run example {} 
run example {} for 5 

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
