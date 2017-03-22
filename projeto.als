module laboratorio

sig lcc {
	computadores: set Computador
}

sig Computador {}
sig ComputadorQuebrado in Computador {}

fact constants {
	#lcc = 2
	#Computador = 20
}

fact {
	all c: Computador | one c.~computadores
	all lab: lcc | #(lab.computadores) = 10

	all lab: lcc | #(lab.computadores & ComputadorQuebrado) < 3
}

pred show[]{
}

run show for 28
