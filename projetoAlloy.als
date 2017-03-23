module laboratorio


------------------------------ASSINATURAS------------------------------

sig lcc {
	computadores: set Computador
}

sig Computador {alunos : set Aluno}
sig ComputadorQuebrado in Computador {}

sig Aluno{}
sig CursoComputacao{alunosMatriculados : set Aluno}

------------------------------FATOS------------------------------
fact constants {
	#lcc = 2
	#Computador = 20
	#CursoComputacao = 1
}

fact {
	all c: Computador | lone c.~computadores
	all a: Aluno | lone a.~alunos
	all lab: lcc | #(lab.computadores) = 10
	all lab: lcc | #(lab.computadores & ComputadorQuebrado) < 3
	all c: ComputadorQuebrado | #c.alunos = 0
	all c: Computador | #c.alunos <= 2
	all c: Computador | one curso: CursoComputacao | c.alunos in curso.alunosMatriculados
} 

------------------------------PREDICADOS(no minimo 3)------------------------------

pred show[]{
}

------------------------------FUNÇÕES(no minimo 3)------------------------------

------------------------------ASSERTS(no minimo 3)------------------------------

------------------------------CHECKS(rodar os asserts aqui)------------------------------
run show for 30
