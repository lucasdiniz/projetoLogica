module laboratorio

open util/ordering[Time]
----------------------ASSINATURAS----------------------

sig Time {}

sig lcc {
	computadores: set Computador
}

abstract sig Computador {
	alunos : set Aluno
}

sig ComputadorFuncionando extends Computador {}

abstract sig ComputadorQuebrado extends Computador {}
sig ComputadorEmReparo extends ComputadorQuebrado {}
sig ComputadorAguardandoReparo extends ComputadorQuebrado {}

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
	all c: ComputadorAguardandoReparo | #c.alunos = 0
	all c: Computador, curso: CursoComputacao | c.alunos in curso.alunosMatriculados
}

----------------------FUNÇÕES----------------------

fun getAlunosMatriculados [cc: CursoComputacao] : set Aluno {
	(cc.alunosMatriculados)
}

fun getTodosComputadores [lab: lcc] : set Computador {
	(lab.computadores)
}

fun getComputadoresQuebrados [lab: lcc] : set Computador {
	(lab.computadores & ComputadorQuebrado)
}

----------------------ASSERTS----------------------

assert testeComputadoresQuebrados {
	all lab: lcc | #(lab.computadores & ComputadorQuebrado) <= 2
}

assert testeAlunosMatriculadosNosComputadores {
	all c: Computador | one curso: CursoComputacao | c.alunos in curso.alunosMatriculados
}

assert testeComputadorQuebradoSemAluno {
	all c: ComputadorAguardandoReparo | #c.alunos = 0
}
----------------------CHECKS----------------------

//check testeComputadoresQuebrados

pred show[]{
}

run show for 30
