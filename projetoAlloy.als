module laboratorio

----------------------ASSINATURAS----------------------

sig lcc {
	computadores: set Computador
}

sig Computador {
	alunos : set Aluno
}
sig ComputadorQuebrado in Computador {}

sig Aluno {}
sig CursoComputacao {
	alunosMatriculados : set Aluno
}

-----------------------FATOS-----------------------

fact constants {
	#lcc = 2
	#Computador = 20
	#CursoComputacao = 1
}

fact computadoresQuebrados {
	all c: Computador | one c.~computadores
	all lab: lcc | #(lab.computadores) = 10
	all lab: lcc | #(lab.computadores & ComputadorQuebrado) <= 2
}

fact aluno {
	all a: Aluno | lone a.~alunos
	all a: Aluno | lone a.~alunosMatriculados
	all c: Computador | #c.alunos <= 2
	all c: ComputadorQuebrado | #c.alunos = 0
	all c: Computador | one curso: CursoComputacao | c.alunos in curso.alunosMatriculados
}

----------------------ASSERTS----------------------

assert testeComputadoresQuebrados {
	#ComputadorQuebrado <= 4
}

----------------------CHECKS----------------------

check testeComputadoresQuebrados

pred show[]{
}

run show for 30
