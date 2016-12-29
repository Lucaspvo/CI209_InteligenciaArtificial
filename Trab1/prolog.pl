elem_repetidos(L, Z):-
	confere(L, [], Z).

confere([], Laux, Laux).
confere([H|T], Laux, Z):-
	pertence_a(H, T),
	not(pertence_a(H, Laux)),
	conc(Laux, H, Lr),
	confere(T, Lr, Z).

confere([H|T], Laux, Z):-
	confere(T, Laux, Z).

conc([], E, E).
conc([H|T], E, [H|Laux]):-
	conc(T, E, Laux).

pertence_a(E, [E|_]).
pertence_a(E, [_|C]):-
	pertence_a(E, C).


intercalada(L1, L2, Z):-
	faz_inter(L1, L2, [], Z).

faz_inter(L1, L2, Laux, Lr):-
	intercala1(L1, L2, Laux, Lr).

intercala1([], [], Laux, Laux).
intercala1([], L2, Laux, Lr):- intercala2([], L2, Laux, Lr).
intercala1([H|T], L2, Laux, Lr):-
	conc(Laux, H, L),
	intercala2(T, L2, L, Lr).

intercala2([], [], Laux, Laux).
intercala2(L1, [], Laux, Lr):- intercala1(L1, [], Laux, Lr).
intercala2(L1, [H|T], Laux, Lr):-
	conc(Laux, H, L),
	intercala1(L1, T, L, Lr).


insercao_ord(E, L, Z):-
	insere(E, L, [], Z).

insere(E, L, La2, Z):-
	divide(E, L, La2, Z).

divide(E, [H|T], La2, Z):-
	E > H,
	divide(E, T, [H|La2], Z).

divide(E, T, La2, Z):-
	invert(La2, [], Lh),
	conc(Lh, [E], L1),
	conc(L1, T, Z).

invert([], Laux, Laux).
invert([H|T], Laux, Lh):-
	invert(T, [H|Laux], Lh).





















