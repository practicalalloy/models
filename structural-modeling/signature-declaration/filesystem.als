module filesystem

abstract sig Object {}

sig Dir extends Object {}
sig File extends Object {}

one sig Root extends Dir {}

sig Entry {}
sig Name {}

run example {}
run example {} for 4
run example {} for 4 but 2 Entry, exactly 3 Name