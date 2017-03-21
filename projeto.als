open util/boolean 

sig lcc {
	computadores : set computador
}


sig computador{
	isBroken : one Bool
}

fact lccNumber{
	#lcc = 2
}
fact numComputadores {
	all lab: lcc | #(lab.computadores) = 10
}

pred show(){}

run show for 10
