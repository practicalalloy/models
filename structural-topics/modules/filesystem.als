module filesystem

open graph[Object]
open timestamp[Object,Timestamp]
open timestamp[Entry,Timestamp]

sig Timestamp {}

fact time {
--	all d:Dir | d.entries.object.(TimeAux.aux_time) in d.(TimeAux.aux_time).*next
	all d:Dir | d.entries.object.time in d.time.*next
}

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
run example {} for 4 but 2 Entry, exactly 3 Name

fact unique_names {
    // Different entries in the same directory must have different names
    all d : Dir, n : Name | lone (d.entries & name.n)
}

fact no_shared_dirs {
    // A directory cannot be contained in more than one entry
    all d : Dir | lone object.d
}

pred no_dangling_objects {
    // Every object except the root is contained somewhere
    Entry.object = Object - Root
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

fact rooted_dag {
--	dag[Object,entries.object]
--	rootedAt[Object,entries.object,Root]
	graph/dag[entries.object]
	rootedAt[entries.object,Root]
}

assert no_partitions {
    // Every object is reachable from the root
    Object - Root = Root.^(entries.object)
}

check no_partitions
check no_partitions for 6
