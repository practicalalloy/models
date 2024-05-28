module filesystem

// Superseded by the enum Permission declaration
// abstract sig Permission {}
// one sig Read, Write, Execute extends Permission {}

enum Permission { Read, Write, Execute }
/*abstract sig Object {
	user_permission : set Permission,
	group_permission : set Permission,
	others_permission : set Permission
}*/


enum Class { User, Group, Other }
sig PermissionAssignment {
	permission : set Permission,
	class : one Class
}

abstract sig Object {
	mode : set PermissionAssignment
}

fact all_classes_assigned {
	all o : Object, c : Class | one o.mode & class.c
}


run distinct_permissions {some disj o1,o2:Object | o1.mode != o2.mode}
run distinct_permissions {
	some disj c1,c2: (class.(User))| c2 in Root.mode and c1.permission = Permission and c2.permission = Read
	(class.(Other)).permission = none
	(class.(Group)).permission = Read
	one File and one Dir
	one Entry
	some disj o1,o2:Object | o1.mode != o2.mode
} for 4 but 2 Entry, exactly 3 Name

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

run example {
--	Root.user_permission = Read
--	group_permission = File -> Permission
--	File.user_permission = Permission
--	others_permission = File -> Permission
	one File and one Dir
	one Entry
}
run example {} for 4 but 2 Entry, exactly 3 Name

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

