open util/ordering[State] as ord // definimos el estado como un conjunto ordenado

sig Semaforo { situacion : set State}
abstract sig Color {}
one sig Rojo, Amarillo, Verde extends Color {}

sig State { luz: one Color }

fun secuenciaColor: set Color -> Color {

	(Rojo->Verde)+(Verde->Amarillo)+(Amarillo->Rojo)+(Color<:iden)
}

pred cambioLuz[e1, e2: State]{ e1.luz -> e2.luz in secuenciaColor}

fact traces{
	init[ord/first]
	all e: State-ord/last | let e1 = e.next | cambioLuz[e,e1]
}


pred init[e:State]{e.luz=Rojo}

pred buscar {ord/last.luz = Amarillo}

pred buscarAlgunEstado { some e:State | e.luz = Amarillo}

run buscar for 9 State, 1 Semaforo
run buscarAlgunEstado for 9 State, 1 Semaforo
