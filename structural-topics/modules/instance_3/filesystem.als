module filesystem
open graph[Object] 
open timestamp[Object,Timestamp]

sig Timestamp {}

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

fact unique_names {
  // Different entries in the same directory must have different names
  all d : Dir, n : Name | lone (d.entries & name.n)
}

fact no_shared_dirs {
  // A directory cannot be contained in more than one entry
  all d : Dir | lone object.d
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

fact rooted_dag {
  dag[entries.object]
  rootedAt[entries.object,Root]
}

fact time {
  all d : Dir | d.entries.object.time in d.time.*next
}

assert no_partitions {
  // Every object is reachable from the root
  all o : Object | reachable[o]
}

check no_partitions
check no_partitions for 6

run book_instance_3 {
  some disj o0,o1,o2,o3,o4,o6,o7 : univ {
    Dir = o0 + o1
    Root = o1
    File = o2
    Entry = o3 + o4
    Name = o6 + o7
--    univ = Object + Entry + File + Timestamp + Int
    entries = o1 -> o3 + o1 -> o4
    name = o3 -> o6 + o4 -> o7
    object = o3 -> o2 + o4 -> o0
  }
}
