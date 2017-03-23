module laboratorio

open util/ordering[Time]
----------------------ASSINATURAS----------------------

sig Time {}

sig lcc {
	computadores: Computador -> Time
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

--fact constants {
	--#lcc = 2
	--#Computador = 20
	--#CursoComputacao = 1
--}

--fact computadoresQuebrados {
	--all c: Computador | one c.~computadores
	--all lab: lcc | #(lab.computadores) = 10
	--all lab: lcc | #(lab.computadores & ComputadorQuebrado) <= 2
--}

--fact aluno {
	--all a: Aluno | lone a.~alunos	all a: Aluno | lone a.~alunosMatriculados
	--all c: Computador | #c.alunos <= 2
	--all c: ComputadorAguardandoReparo | #c.alunos = 0
	--all c: Computador, curso: CursoComputacao | c.alunos in curso.alunosMatriculados
--}

fact traces {
	init[first]
	all pre: Time-last | let pos = pre.next |
		some lab : lcc, c : Computador |
			addComputador[lab, c, pre, pos]
}

----------------------FUNÇÕES----------------------

--fun getAlunosMatriculados [cc: CursoComputacao] : set Aluno {
	--(cc.alunosMatriculados)
--}

--fun getTodosComputadores [lab: lcc] : set Computador -> Time {
	--(lab.computadores)
--}

--fun getComputadoresQuebrados [lab: lcc] : set Computador {
	--(lab.computadores & ComputadorQuebrado)
--}

----------------------ASSERTS----------------------

--assert testeComputadoresQuebrados {
	--all lab: lcc | #(lab.computadores & ComputadorQuebrado) <= 2
--}

--assert testeAlunosMatriculadosNosComputadores {
	--all c: Computador | one curso: CursoComputacao | c.alunos in curso.alunosMatriculados
--}

--assert testeComputadorQuebradoSemAluno {
	--all c: ComputadorAguardandoReparo | #c.alunos = 0
--}
----------------------CHECKS----------------------

//check testeComputadoresQuebrados

pred init[t:Time]	{
	no (lcc.computadores).t
}

pred addComputador[lab:lcc, c:Computador, t, t' : Time] {
	c !in (lab.computadores).t
	(lab.computadores).t' = (lab.computadores).t + c
}

pred show[]{
}

run show
