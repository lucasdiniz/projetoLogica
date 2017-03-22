module laboratorio

-- Assinaturas

sig lcc {
	computadores: set Computador
}

sig Computador {
	alunos : set Aluno
}
sig ComputadorQuebrado in Computador {}

sig Aluno {}
sig Curso {
	alunosMatriculados : set Aluno
}

-- Fatos

fact constants {
	#lcc = 2
	#Computador = 20
}

fact computadoresQuebrados {
	all c: Computador | one c.~computadores
	all lab: lcc | #(lab.computadores) = 10
	all lab: lcc | #(lab.computadores & ComputadorQuebrado) <= 2
}

fact aluno {
	all a: Aluno | one a.~alunos
	all a: Aluno | one a.~alunosMatriculados
	all c: Computador | #c.alunos <= 2
	all c: ComputadorQuebrado | #c.alunos = 0
}

-- Testes

assert testeComputadoresQuebrados {
	#ComputadorQuebrado <= 4
}

check testeComputadoresQuebrados

pred show[]{
}

run show for 30
