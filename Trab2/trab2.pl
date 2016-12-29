% http://www.staff.city.ac.uk/~jacob/solver/sat_solver_freeze.txt
% http://www.staff.city.ac.uk/~jacob/solver/sat_solver_when.txt

:- dynamic
    inicio/2,
    fim/2.

iniciadas_as_instanciacoes:-
    retractall(instanciacoes(_)),
    assertz(instanciacoes(0)).

mais_uma_instanciacao :-
    instanciacoes(N),
    retractall(instanciacoes(_)),
    N2 is N + 1,
    assertz(instanciacoes(N2)).

tempo(Total) :-
    inicio(inicio, Inicio),
    fim(fim, Fim),
    Total is (Fim - Inicio), !.

procura_estrutura(L, [L, Mem], Mem, Achou) :-
    Achou is 1.

procura_estrutura(_, _, _, Achou) :-
    Achou is 0.

procura_mapa(_, [], _, 0).

procura_mapa(L, [H|_], Mem, Achou) :-
    procura_estrutura(L, H, Mem, Achou),
    Achou is 1.

procura_mapa(L, [_|T], Mem, Achou) :-
    procura_mapa(L, T, Mem, Achou).

cria_variavel([H1, H2| T], L, Mapa, Mapa_atualizado) :-
    (
        H1 = 126 ->
            append([[H2], T], C),
            string_codes(X, C),
            procura_mapa(X, Mapa, Mem, Achou),
            (
                Achou = 1 ->
                    L = false-Mem,
                    append(Mapa, [], Mapa_atualizado);

                L = false-Y,
                append([[X, Y]], Mapa, Mapa_atualizado)
            );

        append([H1, H2], T, C),
        string_codes(X, C),
        procura_mapa(X, Mapa, Mem, Achou),
        (
            Achou = 1 ->
                L = true-Mem,
                append(Mapa, [], Mapa_atualizado);

            L = true-Y,
            append([[X, Y]], Mapa, Mapa_atualizado)
        )
    ).

cria_clausula([], L, L, Mapa, Mapa).
cria_clausula([H|T], L, Clausula, Mapa, M) :-
    string_codes(H, Codigos),
    cria_variavel(Codigos, Literal, Mapa, Mapa_atualizado),
    append(L, [Literal], Laux),
    cria_clausula(T, Laux, Clausula, Mapa_atualizado, M).

literais_distintos([], Literais, Literais).
literais_distintos([[_,Literal | _] | Clausulas], L, Literais) :-
    append(L, [Literal], L2),
    literais_distintos(Clausulas, L2, Literais).

cria_variaveis([], Estrutura, Estrutura, Mapa, Literais) :-
    literais_distintos(Mapa, [], Literais).

cria_variaveis([H|T], L, Estrutura, Mapa, Literais) :-
    cria_clausula(H, [], H2, Mapa, Mapa2),
    append([H2], L, L2),
    cria_variaveis(T, L2, Estrutura, Mapa2, Literais).

separa_clausulas(Formula, Parcial) :-
    atomic_list_concat(Parcial, '&', Formula).

separa_literais([], CNF, CNF).
separa_literais([H|T], L, CNF) :-
    atomic_list_concat(H2, '#', H),
    append([H2], L, L2),
    separa_literais(T, L2, CNF).

cria_estrutura(Formula, Estrutura, Literais) :-
    separa_clausulas(Formula, L),
    separa_literais(L, [], L2),
    cria_variaveis(L2, [], Estrutura, [], Literais).

normaliza([], Formula, Formula).
normaliza([H|T], Entrada, Formula) :-
    atomic_list_concat(L, H, Entrada),
    atomic_list_concat(L, Parcial),
    normaliza(T, Parcial, Formula).

instancia_literais_sem_valor([]).
instancia_literais_sem_valor([Literal | T]) :-
    instancia_literais_sem_valor(T),
    (
        Literal = true,
        mais_uma_instanciacao;

        Literal = false,
        mais_uma_instanciacao
    ).

verifica_variavel(Polaridade1, Literal1, Polaridade2, Literal2, Clausulas) :-
    Literal1 == Polaridade1 ->
        true;
    prepara_observacao(Clausulas, Polaridade2, Literal2).

observa_literal(Polaridade1, Literal1, Polaridade2, Literal2, Clausulas) :-
    nonvar(Literal1) ->
        verifica_variavel(Polaridade1, Literal1, Polaridade2, Literal2, Clausulas);
    verifica_variavel(Polaridade2, Literal2, Polaridade1, Literal1, Clausulas).

prepara_observacao([], Polaridade, Literal) :-
    Literal = Polaridade,
    mais_uma_instanciacao.

prepara_observacao([Polaridade2-Literal2 | Clausulas], Polaridade1, Literal1) :-
    when(;(nonvar(Literal1), nonvar(Literal2)),
        observa_literal(Polaridade1, Literal1, Polaridade2, Literal2, Clausulas)
    ).

percorre_clausulas([Polaridade-Literal | Clausulas]) :-
    prepara_observacao(Clausulas, Polaridade, Literal).

dpll([]).
dpll([Clausula | Clausulas]) :-
    percorre_clausulas(Clausula),
    dpll(Clausulas).

prepara_sat(Entrada, Clausulas, Literais) :-
    normaliza([' ', '(', ')'], Entrada, Formula),
    cria_estrutura(Formula, Clausulas, Literais).

verifica_sat(Entrada) :-
    prepara_sat(Entrada, Clausulas, Literais),
    iniciadas_as_instanciacoes,
    !,
    dpll(Clausulas),
    instancia_literais_sem_valor(Literais).

sat(Entrada) :-
    get_time(X),
    assert(inicio(inicio, X)),
    verifica_sat(Entrada),
    get_time(Y),
    assert(fim(fim, Y)),
    tempo(Total),
    write('Tempo de execucao = '), format('~5f', [Total]), write(' segundo(s).'), nl,
    instanciacoes(N),
    write('Instanciacoes = '), write(N), nl,
    !,
    write('Sat'), nl.

sat(_) :-
    get_time(Y),
    assert(fim(fim, Y)),
    tempo(Total),
    write('Tempo de execucao = '), format('~5f', [Total]), write(' segundo(s).'), nl,
    instanciacoes(N),
    write('Instanciacoes = '), write(N), nl,
    write('Unsat'), nl.

testa :-
    retractall(inicio(_,_)), retractall(fim(_,_)), abolish(counter/1),
    write('(x1#x2#x3)&(x1#x2#~x3)&(x1#~x2#x3)&(x1#~x2#~x3)&(~x1#x2#x3)&(~x1#x2#~x3)&(~x1#~x2#x3)&(~x1#~x2#~x3) - UNSAT'),  nl,
    !, sat("(x1#x2#x3)&(x1#x2#~x3)&(x1#~x2#x3)&(x1#~x2#~x3)&(~x1#x2#x3)&(~x1#x2#~x3)&(~x1#~x2#x3)&(~x1#~x2#~x3)"),

    retractall(inicio(_,_)), retractall(fim(_,_)), abolish(counter/1),
    nl, nl, write('x1&~x1 - UNSAT'), nl,
    !, sat("x1&~x1"),

    retractall(inicio(_,_)), retractall(fim(_,_)), abolish(counter/1),
    nl, nl, write('(x1#x1#x1)&(~x1#~x1#~x1) - UNSAT'), nl,
    !, sat("(x1#x1#x1)&(~x1#~x1#~x1)"),

    retractall(inicio(_,_)), retractall(fim(_,_)), abolish(counter/1),
    nl, nl, write('(x1#~x2#x3)&(~x1#x2#x3) - SAT'), nl,
    !, sat("(x1#~x2#x3)&(~x1#x2#x3)"),

    retractall(inicio(_,_)), retractall(fim(_,_)), abolish(counter/1),
    nl, nl, write('(x1#x2#x3)&(x2#x3#x4)&(x3#x4#x5)&(x4#x5#x6)&(x5#x6#x7)&(x6#x7#x8)&(x7#x8#x9)&(x8#x9#x10) - SAT'), nl,
    !, sat("(x1#x2#x3)&(x2#x3#x4)&(x3#x4#x5)&(x4#x5#x6)&(x5#x6#x7)&(x6#x7#x8)&(x7#x8#x9)&(x8#x9#x10)"),

    retractall(inicio(_,_)), retractall(fim(_,_)), abolish(counter/1),
    nl, nl, write('~x1&(x2#x3) - SAT'), nl,
    !, sat("~x1&(x2#x3)"),

    retractall(inicio(_,_)), retractall(fim(_,_)), abolish(counter/1),
    nl, nl, write('(x1#~x3)&(x2#x3#~x1) - SAT'), nl,
    !, sat("(x1#~x3)&(x2#x3#~x1)"),

    retractall(inicio(_,_)), retractall(fim(_,_)), abolish(counter/1),
    nl, nl, write('(x1 # x2) & (~x2 # x3 # ~x4) & (x4 # ~x5) - SAT'), nl,
    !, sat("(x1 # x2) & (~x2 # x3 # ~x4) & (x4 # ~x5)"),

    retractall(inicio(_,_)), retractall(fim(_,_)), abolish(counter/1),
    nl, nl, write('(x1 # x2) & (~x2 # x3 # ~x4) & (x4 # ~x5) & (~x1) - SAT'), nl,
    !, sat("(x1 # x2) & (~x2 # x3 # ~x4) & (x4 # ~x5) & (~x1)"),

    retractall(inicio(_,_)), retractall(fim(_,_)), abolish(counter/1), nl, nl,
    write('(x16#x17#x30)&(~x17#x22#x30)&(~x17#~x22#x30)&(x16#~x30#x47)&(x16#~x30#~x47)&(~x16#~x21#x31)&(~x16#~x21#~x31)&(~x16#x21#~x28)&(~x13#x21#x28)&(x13#~x16#x18)&(x13#~x18#~x38)&(x13#~x18#~x31)&(x31#x38#x44)&(~x8#x31#~x44)&(x8#~x12#~x44)&(x8#x12#~x27)&(x12#x27#x40)&(~x4#x27#~x40)&(x12#x23#~x40)&(~x3#x4#~x23)&(x3#~x23#~x49)&(x3#~x13#~x49)&(~x23#~x26#x49)&(x12#~x34#x49)&(~x12#x26#~x34)&(x19#x34#x36)&(~x19#x26#x36)&(~x30#x34#~x36)&(x24#x34#~x36)&(~x24#~x36#x43)&(x6#x42#~x43)&(~x24#x42#~x43)&(~x5#~x24#~x42)&(x5#x20#~x42)&(x5#~x7#~x20)&(x4#x7#x10)&(~x4#x10#~x20)&(x7#~x10#~x41)&(~x10#x41#x46)&(~x33#x41#~x46)&(x33#~x37#~x46)&(x32#x33#x37)&(x6#~x32#x37)&(~x6#x25#~x32)&(~x6#~x25#~x48)&(~x9#x28#x48)&(~x9#~x25#~x28)&(x19#~x25#x48)&(x2#x9#~x19)&(~x2#~x19#x35)&(~x2#x22#~x35)&(~x22#~x35#x50)&(~x17#~x35#~x50)&(~x29#~x35#~x50)&(~x1#x29#~x50)&(x1#x11#x29)&(~x11#x17#~x45)&(~x11#x39#x45)&(~x26#x39#x45)&(~x3#~x26#x45)&(~x11#x15#~x39)&(x14#~x15#~x39)&(x14#~x15#~x45)&(x14#~x15#~x27)&(~x14#~x15#x47)&(x17#x17#x40)&(x1#~x29#~x31)&(~x7#x32#x38)&(~x14#~x33#~x47)&(~x1#x2#~x8)&(x35#x43#x44)&(x21#x21#x24)&(x20#x29#~x48)&(x23#x35#~x37)&(x2#x18#~x33)&(x15#x25#~x45)&(x9#x14#~x38)&(~x5#x11#x50)&(~x3#~x13#x46)&(~x13#~x41#x43) - SAT'), nl,
    !, sat("(x16#x17#x30)&(~x17#x22#x30)&(~x17#~x22#x30)&(x16#~x30#x47)&(x16#~x30#~x47)&(~x16#~x21#x31)&(~x16#~x21#~x31)&(~x16#x21#~x28)&(~x13#x21#x28)&(x13#~x16#x18)&(x13#~x18#~x38)&(x13#~x18#~x31)&(x31#x38#x44)&(~x8#x31#~x44)&(x8#~x12#~x44)&(x8#x12#~x27)&(x12#x27#x40)&(~x4#x27#~x40)&(x12#x23#~x40)&(~x3#x4#~x23)&(x3#~x23#~x49)&(x3#~x13#~x49)&(~x23#~x26#x49)&(x12#~x34#x49)&(~x12#x26#~x34)&(x19#x34#x36)&(~x19#x26#x36)&(~x30#x34#~x36)&(x24#x34#~x36)&(~x24#~x36#x43)&(x6#x42#~x43)&(~x24#x42#~x43)&(~x5#~x24#~x42)&(x5#x20#~x42)&(x5#~x7#~x20)&(x4#x7#x10)&(~x4#x10#~x20)&(x7#~x10#~x41)&(~x10#x41#x46)&(~x33#x41#~x46)&(x33#~x37#~x46)&(x32#x33#x37)&(x6#~x32#x37)&(~x6#x25#~x32)&(~x6#~x25#~x48)&(~x9#x28#x48)&(~x9#~x25#~x28)&(x19#~x25#x48)&(x2#x9#~x19)&(~x2#~x19#x35)&(~x2#x22#~x35)&(~x22#~x35#x50)&(~x17#~x35#~x50)&(~x29#~x35#~x50)&(~x1#x29#~x50)&(x1#x11#x29)&(~x11#x17#~x45)&(~x11#x39#x45)&(~x26#x39#x45)&(~x3#~x26#x45)&(~x11#x15#~x39)&(x14#~x15#~x39)&(x14#~x15#~x45)&(x14#~x15#~x27)&(~x14#~x15#x47)&(x17#x17#x40)&(x1#~x29#~x31)&(~x7#x32#x38)&(~x14#~x33#~x47)&(~x1#x2#~x8)&(x35#x43#x44)&(x21#x21#x24)&(x20#x29#~x48)&(x23#x35#~x37)&(x2#x18#~x33)&(x15#x25#~x45)&(x9#x14#~x38)&(~x5#x11#x50)&(~x3#~x13#x46)&(~x13#~x41#x43)"),

    retractall(inicio(_,_)), retractall(fim(_,_)), abolish(counter/1), nl, nl,
    write('(x1#x2)&(~x2#~x4)&(x3#x4)&(~x4#~x5)&(x5#~x6)&(x6#~x7)&(x6#x7)&(x7#~x16)&(x8#~x9)&(~x8#~x14)&(x9#x10)&(x9#~x10)&(~x10#~x11)&(x10#x12)&(x11#x12)&(x13#x14)&(x14#~x15)&(x15#x16) - SAT'), nl,
    !,
    sat("(x1#x2)&(~x2#~x4)&(x3#x4)&(~x4#~x5)&(x5#~x6)&(x6#~x7)&(x6#x7)&(x7#~x16)&(x8#~x9)&(~x8#~x14)&(x9#x10)&(x9#~x10)&(~x10#~x11)&(x10#x12)&(x11#x12)&(x13#x14)&(x14#~x15)&(x15#x16)"),

    retractall(inicio(_,_)), retractall(fim(_,_)), abolish(counter/1).
