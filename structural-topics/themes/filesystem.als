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

run example {
	one File
	# (Dir - Root) = 2
	some entries.univ & Dir - Root
	some entries.univ & Root
	entries.univ != Dir
	#Name = 3
  	some Root.entries.object & File
	one object.File
} for 4
run example {} for 4 but 2 Entry, exactly 3 Name

fun empty_dirs : set Dir {
   Dir - entries.Entry
}

fun contents : Dir -> Object {
   entries.object
}

fun named_contents : Dir -> Name -> Object {
   { d : Dir, n : Name, o : Object | 
      some e : Entry | e in d.entries and e.name = n and e.object = o } 
}
