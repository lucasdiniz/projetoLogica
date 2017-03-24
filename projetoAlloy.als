module laboratorio

open util/ordering[Time]
----------------------ASSINATURAS----------------------

sig Time {}

sig lcc {
	computadoresFuncionais: set Computador -> Time,
	computadoresQuebrados: set Computador -> Time,
	computadoresReparo: set Computador -> Time,
	computadoresAguardandoReparo: set Computador -> Time
}

--abstract sig Computador {
sig Computador {
	alunos : set Aluno -> Time
}

--sig ComputadorFuncionando extends Computador {}

--abstract sig ComputadorQuebrado extends Computador {}
--sig ComputadorEmReparo extends ComputadorQuebrado {}
--sig ComputadorAguardandoReparo extends ComputadorQuebrado {}

sig Aluno {} 
sig CursoComputacao {
	alunosMatriculados : set Aluno -> Time
}

-----------------------FATOS-----------------------

fact constants {
	#lcc = 2
	#Computador = 20
	#CursoComputacao = 1
}

fact computadoresQuebrados {
	all c: Computador, t: Time | one c.~((computadoresFuncionais + computadoresQuebrados + computadoresReparo + computadoresAguardandoReparo).t)
	all lab: lcc, t: Time| #todosComputadoresLab[lab, t] = 10
	all lab: lcc, t: Time | #computadoresQuebradosLab[lab, t] <= 2
	all lab: lcc, t: Time | #computadoresEmReparoLab[lab, t] <= 2
}

fact aluno {
	all a: Aluno, t: Time | lone a.~(alunosMatriculados.t) and lone a.~(alunos.t)
	all c: Computador, t: Time | #(c.alunos).t <= 2
	all lab: lcc, c: Computador, t: Time | c in t.~(lab.computadoresAguardandoReparo) => #c.alunos = 0
	all c: Computador, curso: CursoComputacao | c.alunos in curso.alunosMatriculados
}

fact traces {
	init[first]
	all pre: Time-last | let pos = pre.next |
		some lab : lcc,c : Computador, a:Aluno |
			addAlunoComputador[c, a, pre, pos] or
			computadorQuebrou[lab, c, pre, pos]  or
			aguardarReparo[lab, c, pre, pos]  or
			iniciarReparo[lab, c, pre, pos]  or
			reparaComputador[lab, c, pre, pos]
}

----------------------FUNÇÕES----------------------

fun alunosMatriculadosCurso [cc: CursoComputacao, t: Time] : set Aluno {
	(cc.alunosMatriculados).t
}

fun todosComputadoresLab [lab: lcc, t: Time] : set Computador {
	(lab.computadoresFuncionais + lab.computadoresQuebrados + lab.computadoresReparo + lab.computadoresReparo).t
}

fun computadoresQuebradosLab [lab: lcc, t: Time] : set Computador {
	(lab.computadoresQuebrados).t
}

fun computadoresEmReparoLab [lab: lcc, t: Time] : set Computador {
	(lab.computadoresReparo).t
}

----------------------ASSERTS----------------------

assert testeComputadoresQuebrados {
	all lab: lcc, t: Time | #computadoresQuebradosLab[lab, t] <= 2
}

assert testeAlunosMatriculadosNosComputadores {
	all c: Computador, curso: CursoComputacao, t: Time | #((c.alunos).t & (curso.alunosMatriculados).t) = #(c.alunos).t
}

assert testeComputadorQuebradoSemAluno {
	all lab: lcc, c: Computador, t: Time | c in t.~(lab.computadoresAguardandoReparo) and #c.alunos = 0
}

----------------------CHECKS----------------------

//check testeComputadoresQuebrados

pred init[t:Time]	{
	all lab: lcc | #(lab.computadoresFuncionais).t = 10
	all c:Computador | no (c.alunos).t
}	

pred addAlunoComputador[c:Computador, a:Aluno,  t, t': Time] {
	a !in (c.alunos).t
	(c.alunos).t' = (c.alunos).t + a 
}

pred computadorQuebrou[lab:lcc, c:Computador, t, t' : Time] {
	c in (lab.computadoresFuncionais).t
	c !in (lab.computadoresQuebrados).t
	(lab.computadoresFuncionais).t' = (lab.computadoresFuncionais).t - c
	(lab.computadoresQuebrados).t' = (lab.computadoresQuebrados).t + c
}

pred aguardarReparo[lab:lcc, c:Computador, t, t' : Time] {
	c in (lab.computadoresQuebrados).t
	c !in (lab.computadoresAguardandoReparo).t
	(lab.computadoresAguardandoReparo).t' = (lab.computadoresQuebrados).t + c
	(lab.computadoresQuebrados).t' = (lab.computadoresQuebrados).t - c
}

pred iniciarReparo [lab:lcc, c: Computador, t, t' : Time] {
	c in (lab.computadoresAguardandoReparo).t
	c !in (lab.computadoresReparo).t
	(lab.computadoresReparo).t' = (lab.computadoresReparo).t + c
	(lab.computadoresAguardandoReparo).t' = (lab.computadoresAguardandoReparo).t - c
}

pred reparaComputador[lab:lcc, c:Computador, t, t' : Time] {
	c in (lab.computadoresReparo).t
	c !in (lab.computadoresFuncionais).t
	(lab.computadoresFuncionais).t' = (lab.computadoresReparo).t + c
	(lab.computadoresReparo).t' = (lab.computadoresFuncionais).t - c
}

pred show[]{}

run show for 5 but exactly 20 Computador
