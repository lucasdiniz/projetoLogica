module laboratorio

sig lcc {
	computadores: set Computador
}

sig Computador {alunos : set Aluno}
sig ComputadorQuebrado in Computador {}

sig Aluno{}
sig Curso{alunosMatriculados : set Aluno}

fact constants {
	#lcc = 2
	#Computador = 20
}

fact {
	all c: Computador | one c.~computadores
	all a: Aluno | one a.~alunos
	all lab: lcc | #(lab.computadores) = 10
	all lab: lcc | #(lab.computadores & ComputadorQuebrado) < 3
	all c: ComputadorQuebrado | #c.alunos = 0
	all c: Computador | all a: Aluno | one a.~alunosMatriculados |  #c.alunos <= 2
} 

pred show[]{
}

run show for 30
