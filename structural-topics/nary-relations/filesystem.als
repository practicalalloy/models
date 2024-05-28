module filesystem

abstract sig Object {}

sig Dir extends Object {
    contents : Name -> lone Object
}

sig File extends Object {}

one sig Root extends Dir {}

sig Name {}

run example {}
run example {
	#(Root.contents)=2
	#((Dir - Root).contents) = 2
	# File = 1 -- = 2
	# (Dir - Root) = 2
	File in univ.(univ.contents)
--	Root in univ.(univ.contents)
} for 4 but exactly 3 Name

/* Superseded by multiplicity lone
fact unique_names {
    // Different entries in the same directory must have different names
    all d : Dir, n : Name | lone n.(d.contents)
}
*/

fact no_shared_dirs {
    // A directory cannot be contained in more than one entry
    all d : Dir | lone contents.d
}

fact no_dangling_objects {
    // Every object except the root is contained somewhere
    Name.(Object.contents) = Object - Root
}

fun objects : Dir -> Object {
	{ d : Dir, o : Object | some d.contents.o }
}

fun descendants [o : Object] : set Object {
    o.^objects
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
