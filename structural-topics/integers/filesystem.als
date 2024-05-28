module filesystem

abstract sig Object {}

sig Dir extends Object {
    entries : set Entry
}

sig File extends Object {
	size: one Int
}

one sig Root extends Dir {}

sig Entry {
    object : one Object,
    name   : one Name
}

sig Name {}

one sig Capacity in Int {}

run full_root { 
Capacity = 7
#(Root.entries) = 3 
#File = 3
} for 4

fact size_limits {
	all f : File | f.size <= div[max,#File]
}

run example {
--	some o1,o2,o3:File | o1.size = -1 and o2.size = 7 and o3.size = 2
	some o1,o2,o3:File | o1.size = 2 and o2.size = 7 and o3.size = 2
	Capacity = 4
	#Entry = 3
	#File = 3

} for 4 but 4 Int
run example {

} for 4 but 2 Entry, exactly 3 Name

check big_files { 
  all f:File | f.size > 10 
} for 10

fact positive_sizes {
  // All file sizes are positive
  all f : File | gt[f.size,0]
}

fact below_capactiy {
  // The sum of the size of all files cannot exceed the capacity
  (sum f : File | f.size) <= Capacity
}

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

