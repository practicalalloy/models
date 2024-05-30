module filesystem

abstract sig Object {}

sig Dir extends Object {
    contents : Name -> Object
}

sig File extends Object {}

one sig Root extends Dir {}

sig Name {}

run example {}
run example {} for 4
run example {} for 4 but exactly 3 Name
