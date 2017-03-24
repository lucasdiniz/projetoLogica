module laboratorio

open util/ordering[Time]

----------------------ASSINATURAS----------------------

sig Time {}

sig lcc {
	computadoresFuncionais: set Computador -> Time,
	computadoresQuebrados: set Computador -> Time,
	computadoresEmReparo: set Computador -> Time
}

sig Computador {
	alunos : set Aluno -> Time
}

sig Aluno {}

abstract sig Curso {
	alunosMatriculados : set Aluno -> Time
}

sig CursoComputacao extends Curso{}
-----------------------FATOS-----------------------

fact constants {
	#lcc = 2
	#Computador = 20
	#CursoComputacao = 1
}

fact computadoresQuebrados {
	all c: Computador, t: Time | one c.~((computadoresFuncionais + computadoresQuebrados + computadoresEmReparo).t)
	some lab: lcc, t: Time, c: Computador | (c in (lab. computadoresFuncionais).t) or (c in (lab.computadoresQuebrados).t) or (c in (lab.computadoresEmReparo).t)
	all lab: lcc, c: Computador, t: Time | c in (lab.computadoresQuebrados + lab.computadoresEmReparo).t => c !in lab.computadoresFuncionais.t
	all lab: lcc, c: Computador, t: Time | c in (lab.computadoresQuebrados).t  => c !in lab.computadoresFuncionais.t and c !in lab.computadoresEmReparo.t
	all lab: lcc, t: Time | #todosComputadoresLab[lab, t] = 10
	all lab: lcc, t: Time | #computadoresInativos[lab, t] <= 2
}

fact aluno {
	all a: Aluno, t: Time | lone a.~(alunosMatriculados.t) and lone a.~(alunos.t)
	all c: Computador, t: Time | #(c.alunos).t <= 2
	--all lab: lcc, c: Computador, t: Time | c in t.~(lab.computadoresAguardandoReparo) => #c.alunos = 0
	all c: Computador, curso: CursoComputacao | c.alunos in curso.alunosMatriculados
    all t': Time, c:Computador, lab: lcc | c in (lab.computadoresEmReparo).t' => some t: t'.^prev | c in (lab.computadoresQuebrados).t 
}

fact traces {
	init[first]
	all pre: Time-last | let pos = pre.next |
		some lab : lcc,c : Computador, a:Aluno |
			addAlunoComputador[lab, c, a, pre, pos]  or
			computadorQuebrou[lab, c, pre, pos] or
			iniciarReparo[lab, c, pre, pos]     or
			reparaComputador[lab, c, pre, pos]
}

----------------------FUNÇÕES----------------------

fun alunosMatriculadosCurso [cc: CursoComputacao, t: Time] : set Aluno {
	(cc.alunosMatriculados).t
}

fun todosComputadoresLab [lab: lcc, t: Time] : set Computador {
	(lab.computadoresFuncionais + lab.computadoresQuebrados + lab.computadoresEmReparo).t
}

fun computadoresQuebradosLab [lab: lcc, t: Time] : set Computador {
	(lab.computadoresQuebrados).t
}

fun computadoresEmReparoLab [lab: lcc, t: Time] : set Computador {
	(lab.computadoresEmReparo).t
}

fun computadoresInativos [lab:lcc, t:Time] : set Computador {
	(lab.computadoresQuebrados + lab.computadoresEmReparo).t
}

----------------------ASSERTS----------------------

assert testeComputadoresQuebrados {
	all lab: lcc, t: Time | #computadoresQuebradosLab[lab, t] <= 2
}

assert testeAlunosMatriculadosNosComputadores {
	all c: Computador, curso: CursoComputacao, t: Time | #((c.alunos).t & (curso.alunosMatriculados).t) = #(c.alunos).t
}

assert testeComputadorQuebradoSemAluno {
--	all lab: lcc, c: Computador, t: Time | c in t.~(lab.computadoresAguardandoReparo) and #c.alunos = 0
}

----------------------PREDICADOS-------------------

pred init[t:Time]	{
	all lab: lcc | #(lab.computadoresFuncionais).t = 10
	all c:Computador | no (c.alunos).t
	all lab:lcc | #(lab.computadoresQuebrados + lab.computadoresEmReparo).t = 0
	--all lab:lcc, c:ComputadorQuebrado | c not in (lab.computadoresFuncionais).t
}	

pred addAlunoComputador[lab:lcc, c:Computador, a:Aluno,  t, t': Time] {
	a !in (c.alunos).t
	(c.alunos).t' = (c.alunos).t + a
	(lab.computadoresFuncionais).t' = (lab.computadoresFuncionais).t
	(lab.computadoresQuebrados).t' = (lab.computadoresQuebrados).t
	(lab.computadoresEmReparo).t' = (lab.computadoresEmReparo).t
	 
}

pred computadorQuebrou[lab:lcc, c:Computador, t, t' : Time] {
    (c.alunos).t' = (c.alunos).t 
	c in (lab.computadoresFuncionais).t
	c !in (lab.computadoresQuebrados).t
	c !in (lab.computadoresEmReparo).t
	(lab.computadoresFuncionais).t' = (lab.computadoresFuncionais).t - c
	(lab.computadoresQuebrados).t' = (lab.computadoresQuebrados).t + c
	(lab.computadoresEmReparo).t' = (lab.computadoresEmReparo).t
}

pred iniciarReparo[lab:lcc, c:Computador, t, t' : Time] {
    (c.alunos).t' = (c.alunos).t 
 	c in (lab.computadoresQuebrados).t
 	c !in (lab.computadoresEmReparo).t
	c !in (lab.computadoresFuncionais).t
	(lab.computadoresEmReparo).t' = (lab.computadoresEmReparo).t + c
 	(lab.computadoresQuebrados).t' = (lab.computadoresQuebrados).t - c
	(lab.computadoresFuncionais).t' = (lab.computadoresFuncionais).t
 }

pred reparaComputador[lab:lcc, c:Computador, t, t' : Time] {
    (c.alunos).t' = (c.alunos).t 
	c in (lab.computadoresEmReparo).t
	c !in (lab.computadoresFuncionais).t
	c !in (lab.computadoresQuebrados).t
	(lab.computadoresFuncionais).t' = (lab.computadoresFuncionais).t + c
	(lab.computadoresEmReparo).t' = (lab.computadoresEmReparo).t - c
	(lab.computadoresQuebrados).t' = (lab.computadoresQuebrados).t
}

pred show[]{}

run show for 10 but exactly 20 Computador
