module timestamp[A,T]
open util/ordering[T]

private one sig TimeAux {
	aux_time : A -> T
}

fact {
	TimeAux.aux_time in A -> one T
}

fun time : A -> T {
	TimeAux.aux_time
}

run {} for 5 A, 5 T
