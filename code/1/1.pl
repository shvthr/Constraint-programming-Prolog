% suggested query: main.

:- use_module(library(clpfd)).

main :-
	solutions
	;
	halt.

main2 :-
	solutions
	;
	fail.

solutions :-
	statistics(runtime,_),
	fd_statistics(backtracks,_),
	write('=========================[ Solutions ]========================='),
	nl,
	(	the_problem(__S),
		write('[X,Y,Z] = '), write(__S),
		nl,
		fail
	;
		write('=======================[ End Solutions ]======================='),
		nl,
		fail
	).

the_problem([X,Y,Z]) :-
	length(X,4),
	domain(X,2,6),
	numbered_list(X,XL,1),
	length(Y,6),
	domain(Y,1,5),
	numbered_list(Y,YL,1),
	length(Z,2),
	domain(Z,0,1),
	numbered_list(Z,ZL,1),
	all_constraints([XL,YL,ZL]),
	myappend([],X,__Tmp1),
	myappend(__Tmp1,Y,__Tmp2),
	myappend(__Tmp2,Z,__Tmp3),
	labeling([leftmost, step, up], __Tmp3),
	fd_statistics(backtracks,__BT),
	write('Backtracks: '), write(__BT), nl,
	statistics(runtime,[_,__RT]),
	__RTsec is __RT / 1000,
	write('Runtime: '), write(__RTsec), write('s'), nl.

find_var([(V,N)|_], N, V) :- !.
find_var([_|Vs], N, V) :-
	find_var(Vs, N, V).

numbered_list([X],[(X,Acc)],Acc) :- !.
numbered_list([X|Xs],[(X,Acc)|XNs],Acc) :-
	Acc1 is Acc + 1,
	numbered_list(Xs,XNs,Acc1).

myappend([],L,L).
myappend([X|L1],L2,[X|L12]) :-
	myappend(L1,L2,L12).

all_constraints([X,Y,Z]) :-
	write('Adding constraint "'), write('X_I mod 2 = 0"'), write(' for values:'), nl,
	the_constraint1(X),
	write('Adding constraint "'), write('Y_I mod 2 = 1"'), write(' for values:'), nl,
	the_constraint2(Y),
	write('Adding constraint "'), write('X_I + Y_I = Y_J + 10 * Z_I"'), write(' for values:'), nl,
	the_constraint3(X,Y,Y,Z),
	write('Adding constraint "'), write('Z_I + X_J + Y_K = X_K + 10*Z_J"'), write(' for values:'), nl,
	the_constraint4(Z,X,Y,X,Z),
	write('Adding constraint "'), write('Z_I + Y_J + X_J  =Y_K + 10*Y_L"'), write(' for values:'), nl,
	the_constraint5(Z,Y,X,Y,Y).

the_constraint1([]).
the_constraint1([X_I|X_Is]) :-
	the_constraint1_aux(X_I),
	the_constraint1(X_Is).

the_constraint1_aux((X_I,I)) :- !,
	((I >= 1 , I =< 4 ) ->
		write('\t'),
		write('I='), write(I), write(', '),
		nl,
		X_I mod 2 #= 0
	;
		true
	).
the_constraint1_aux(_).

the_constraint2([]).
the_constraint2([Y_I|Y_Is]) :-
	the_constraint2_aux(Y_I),
	the_constraint2(Y_Is).

the_constraint2_aux((Y_I,I)) :- !,
	((I >= 1 , I =< 6) ->
		write('\t'),
		write('I='), write(I), write(', '),
		nl,
		Y_I mod 2 #= 1
	;
		true
	).
the_constraint2_aux(_).

the_constraint3([],_,_,_).
the_constraint3([X_I|X_Is],Y_I,Y_J,Z_I) :-
	the_constraint3_aux(X_I,Y_I,Y_J,Z_I),
	the_constraint3(X_Is,Y_I,Y_J,Z_I).

the_constraint3_aux(_,[],_,_).
the_constraint3_aux(X_I,[Y_I|Y_Is],Y_J,Z_I) :-
	the_constraint3_aux_aux(X_I,Y_I,Y_J,Z_I),
	the_constraint3_aux(X_I,Y_Is,Y_J,Z_I).

the_constraint3_aux_aux(_,_,[],_).
the_constraint3_aux_aux(X_I,Y_I,[Y_J|Y_Js],Z_I) :-
	the_constraint3_aux_aux_aux(X_I,Y_I,Y_J,Z_I),
	the_constraint3_aux_aux(X_I,Y_I,Y_Js,Z_I).

the_constraint3_aux_aux_aux(_,_,_,[]).
the_constraint3_aux_aux_aux(X_I,Y_I,Y_J,[Z_I|Z_Is]) :-
	the_constraint3_aux_aux_aux_aux(X_I,Y_I,Y_J,Z_I),
	the_constraint3_aux_aux_aux(X_I,Y_I,Y_J,Z_Is).

the_constraint3_aux_aux_aux_aux((X_I,I), (Y_I,I), (Y_J,J), (Z_I,I)) :- !,
	(I =:= 1 , J =:= 2 ->
		write('\t'),
		write('I='), write(I), write(', '),
		write('I='), write(I), write(', '),
		write('J='), write(J), write(', '),
		write('I='), write(I), write(', '),
		nl,
		X_I + Y_I #= Y_J + 10 * Z_I
	;
		true
	).
the_constraint3_aux_aux_aux_aux(_,_,_,_).

the_constraint4([],_,_,_,_).
the_constraint4([Z_I|Z_Is],X_J,Y_K,X_K,Z_J) :-
	the_constraint4_aux(Z_I,X_J,Y_K,X_K,Z_J),
	the_constraint4(Z_Is,X_J,Y_K,X_K,Z_J).

the_constraint4_aux(_,[],_,_,_).
the_constraint4_aux(Z_I,[X_J|X_Js],Y_K,X_K,Z_J) :-
	the_constraint4_aux_aux(Z_I,X_J,Y_K,X_K,Z_J),
	the_constraint4_aux(Z_I,X_Js,Y_K,X_K,Z_J).

the_constraint4_aux_aux(_,_,[],_,_).
the_constraint4_aux_aux(Z_I,X_J,[Y_K|Y_Ks],X_K,Z_J) :-
	the_constraint4_aux_aux_aux(Z_I,X_J,Y_K,X_K,Z_J),
	the_constraint4_aux_aux(Z_I,X_J,Y_Ks,X_K,Z_J).

the_constraint4_aux_aux_aux(_,_,_,[],_).
the_constraint4_aux_aux_aux(Z_I,X_J,Y_K,[X_K|X_Ks],Z_J) :-
	the_constraint4_aux_aux_aux_aux(Z_I,X_J,Y_K,X_K,Z_J),
	the_constraint4_aux_aux_aux(Z_I,X_J,Y_K,X_Ks,Z_J).

the_constraint4_aux_aux_aux_aux(_,_,_,_,[]).
the_constraint4_aux_aux_aux_aux(Z_I,X_J,Y_K,X_K,[Z_J|Z_Js]) :-
	the_constraint4_aux_aux_aux_aux_aux(Z_I,X_J,Y_K,X_K,Z_J),
	the_constraint4_aux_aux_aux_aux(Z_I,X_J,Y_K,X_K,Z_Js).

the_constraint4_aux_aux_aux_aux_aux((Z_I,I), (X_J,J), (Y_K,K), (X_K,K), (Z_J,J)) :- !,
	(I =:= 1 , J =:= 2 , K =:= 3 ->
		write('\t'),
		write('I='), write(I), write(', '),
		write('J='), write(J), write(', '),
		write('K='), write(K), write(', '),
		write('K='), write(K), write(', '),
		write('J='), write(J), write(', '),
		nl,
		Z_I + X_J + Y_K #= X_K + 10*Z_J
	;
		true
	).
the_constraint4_aux_aux_aux_aux_aux(_,_,_,_,_).

the_constraint5([],_,_,_,_).
the_constraint5([Z_I|Z_Is],Y_J,X_J,Y_K,Y_L) :-
	the_constraint5_aux(Z_I,Y_J,X_J,Y_K,Y_L),
	the_constraint5(Z_Is,Y_J,X_J,Y_K,Y_L).

the_constraint5_aux(_,[],_,_,_).
the_constraint5_aux(Z_I,[Y_J|Y_Js],X_J,Y_K,Y_L) :-
	the_constraint5_aux_aux(Z_I,Y_J,X_J,Y_K,Y_L),
	the_constraint5_aux(Z_I,Y_Js,X_J,Y_K,Y_L).

the_constraint5_aux_aux(_,_,[],_,_).
the_constraint5_aux_aux(Z_I,Y_J,[X_J|X_Js],Y_K,Y_L) :-
	the_constraint5_aux_aux_aux(Z_I,Y_J,X_J,Y_K,Y_L),
	the_constraint5_aux_aux(Z_I,Y_J,X_Js,Y_K,Y_L).

the_constraint5_aux_aux_aux(_,_,_,[],_).
the_constraint5_aux_aux_aux(Z_I,Y_J,X_J,[Y_K|Y_Ks],Y_L) :-
	the_constraint5_aux_aux_aux_aux(Z_I,Y_J,X_J,Y_K,Y_L),
	the_constraint5_aux_aux_aux(Z_I,Y_J,X_J,Y_Ks,Y_L).

the_constraint5_aux_aux_aux_aux(_,_,_,_,[]).
the_constraint5_aux_aux_aux_aux(Z_I,Y_J,X_J,Y_K,[Y_L|Y_Ls]) :-
	the_constraint5_aux_aux_aux_aux_aux(Z_I,Y_J,X_J,Y_K,Y_L),
	the_constraint5_aux_aux_aux_aux(Z_I,Y_J,X_J,Y_K,Y_Ls).

the_constraint5_aux_aux_aux_aux_aux((Z_I,I), (Y_J,J), (X_J,J), (Y_K,K), (Y_L,L)) :- !,
	(I =:= 2 , J =:= 4 , K =:= 5 , L =:= 6 ->
		write('\t'),
		write('I='), write(I), write(', '),
		write('J='), write(J), write(', '),
		write('J='), write(J), write(', '),
		write('K='), write(K), write(', '),
		write('L='), write(L), write(', '),
		nl,
		Z_I + Y_J + X_J  #=Y_K + 10*Y_L
	;
		true
	).
the_constraint5_aux_aux_aux_aux_aux(_,_,_,_,_).

