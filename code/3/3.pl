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
		write('[S1C,S1R,S2C,S2R,S3C,S3R,S4C,S4R,Col,Row,Z] = '), write(__S),
		nl,
		fail
	;
		write('=======================[ End Solutions ]======================='),
		nl,
		fail
	).

the_problem([S1C,S1R,S2C,S2R,S3C,S3R,S4C,S4R,Col,Row,Z]) :-
	S1C in 0..3,
	S1R in 0..1,
	S2C in 0..5,
	S2R in 0..2,
	S3C in 0..4,
	S3R in 0..3,
	S4C in 0..2,
	S4R in 0..3,
	length(Col,28),
	domain(Col,0,6),
	numbered_list(Col,ColL,0),
	length(Row,28),
	domain(Row,0,3),
	numbered_list(Row,RowL,0),
	length(Z,28),
	domain(Z,0,4),
	numbered_list(Z,ZL,0),
	all_constraints([S1C,S1R,S2C,S2R,S3C,S3R,S4C,S4R,ColL,RowL,ZL]),
	myappend([S1C,S1R,S2C,S2R,S3C,S3R,S4C,S4R],Col,__Tmp1),
	myappend(__Tmp1,Row,__Tmp2),
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

all_constraints([S1C,S1R,S2C,S2R,S3C,S3R,S4C,S4R,Col,Row,Z]) :-
	write('Adding constraint "'), write('Col_I = I mod 7"'), write(' for values:'), nl,
	the_constraint1(Col),
	write('Adding constraint "'), write('Row_I = I / 7"'), write(' for values:'), nl,
	the_constraint2(Row),
	write('Adding constraint "'), write('Z_I = 1 <=> (Col_I - 3 =< S1C /\\ S1C =<  Col_I /\\ Row_I -2 =< S1R /\\ S1R=< Row_I)"'), write(' for values:'), nl,
	the_constraint3(Z,Col,Row,S1C,S1C,S1R,S1R),
	write('Adding constraint "'), write('Z_I = 2 <=> (Col_I - 1 =< S2C /\\ S2C =<  Col_I /\\ Row_I -1 =< S2R /\\ S2R=< Row_I)"'), write(' for values:'), nl,
	the_constraint4(Z,Col,Row,S2C,S2C,S2R,S2R),
	write('Adding constraint "'), write('Z_I = 3 <=> (Col_I - 2 =< S3C /\\ S3C =<  Col_I /\\ S3R= Row_I)"'), write(' for values:'), nl,
	the_constraint5(Z,Col,Row,S3C,S3C,S3R),
	write('Adding constraint "'), write('Z_I = 4 <=> (Col_I - 4 =< S4C /\\ S4C =<  Col_I /\\ Row_I = S4R)"'), write(' for values:'), nl,
	the_constraint6(Z,Col,Row,S4C,S4C,S4R).

the_constraint1([]).
the_constraint1([Col_I|Col_Is]) :-
	the_constraint1_aux(Col_I),
	the_constraint1(Col_Is).

the_constraint1_aux((Col_I,I)) :- !,
	(0 =< I , I=< 27 ->
		write('\t'),
		write('I='), write(I), write(', '),
		nl,
		Col_I #= I mod 7
	;
		true
	).
the_constraint1_aux(_).

the_constraint2([]).
the_constraint2([Row_I|Row_Is]) :-
	the_constraint2_aux(Row_I),
	the_constraint2(Row_Is).

the_constraint2_aux((Row_I,I)) :- !,
	(0 =< I , I =< 27 ->
		write('\t'),
		write('I='), write(I), write(', '),
		nl,
		Row_I #= I / 7
	;
		true
	).
the_constraint2_aux(_).

the_constraint3([],_,_,_,_,_,_).
the_constraint3([Z_I|Z_Is],Col_I,Row_I,S1C,S1C,S1R,S1R) :-
	the_constraint3_aux(Z_I,Col_I,Row_I,S1C,S1C,S1R,S1R),
	the_constraint3(Z_Is,Col_I,Row_I,S1C,S1C,S1R,S1R).

the_constraint3_aux(_,[],_,_,_,_,_).
the_constraint3_aux(Z_I,[Col_I|Col_Is],Row_I,S1C,S1C,S1R,S1R) :-
	the_constraint3_aux_aux(Z_I,Col_I,Row_I,S1C,S1C,S1R,S1R),
	the_constraint3_aux(Z_I,Col_Is,Row_I,S1C,S1C,S1R,S1R).

the_constraint3_aux_aux(_,_,[],_,_,_,_).
the_constraint3_aux_aux(Z_I,Col_I,[Row_I|Row_Is],S1C,S1C,S1R,S1R) :-
	the_constraint3_aux_aux_aux(Z_I,Col_I,Row_I,S1C,S1C,S1R,S1R),
	the_constraint3_aux_aux(Z_I,Col_I,Row_Is,S1C,S1C,S1R,S1R).

the_constraint3_aux_aux_aux((Z_I,I), (Col_I,I), (Row_I,I), S1C, S1C, S1R, S1R) :- !,
	(0 =< I , I =< 27 ->
		write('\t'),
		write('I='), write(I), write(', '),
		write('I='), write(I), write(', '),
		write('I='), write(I), write(', '),
		nl,
		Z_I #= 1 #<=> (Col_I - 3 #=< S1C #/\ S1C #=<  Col_I #/\ Row_I -2 #=< S1R #/\ S1R#=< Row_I)
	;
		true
	).
the_constraint3_aux_aux_aux(_,_,_,_,_,_,_).

the_constraint4([],_,_,_,_,_,_).
the_constraint4([Z_I|Z_Is],Col_I,Row_I,S2C,S2C,S2R,S2R) :-
	the_constraint4_aux(Z_I,Col_I,Row_I,S2C,S2C,S2R,S2R),
	the_constraint4(Z_Is,Col_I,Row_I,S2C,S2C,S2R,S2R).

the_constraint4_aux(_,[],_,_,_,_,_).
the_constraint4_aux(Z_I,[Col_I|Col_Is],Row_I,S2C,S2C,S2R,S2R) :-
	the_constraint4_aux_aux(Z_I,Col_I,Row_I,S2C,S2C,S2R,S2R),
	the_constraint4_aux(Z_I,Col_Is,Row_I,S2C,S2C,S2R,S2R).

the_constraint4_aux_aux(_,_,[],_,_,_,_).
the_constraint4_aux_aux(Z_I,Col_I,[Row_I|Row_Is],S2C,S2C,S2R,S2R) :-
	the_constraint4_aux_aux_aux(Z_I,Col_I,Row_I,S2C,S2C,S2R,S2R),
	the_constraint4_aux_aux(Z_I,Col_I,Row_Is,S2C,S2C,S2R,S2R).

the_constraint4_aux_aux_aux((Z_I,I), (Col_I,I), (Row_I,I), S2C, S2C, S2R, S2R) :- !,
	(0 =< I , I =< 27 ->
		write('\t'),
		write('I='), write(I), write(', '),
		write('I='), write(I), write(', '),
		write('I='), write(I), write(', '),
		nl,
		Z_I #= 2 #<=> (Col_I - 1 #=< S2C #/\ S2C #=<  Col_I #/\ Row_I -1 #=< S2R #/\ S2R#=< Row_I)
	;
		true
	).
the_constraint4_aux_aux_aux(_,_,_,_,_,_,_).

the_constraint5([],_,_,_,_,_).
the_constraint5([Z_I|Z_Is],Col_I,Row_I,S3C,S3C,S3R) :-
	the_constraint5_aux(Z_I,Col_I,Row_I,S3C,S3C,S3R),
	the_constraint5(Z_Is,Col_I,Row_I,S3C,S3C,S3R).

the_constraint5_aux(_,[],_,_,_,_).
the_constraint5_aux(Z_I,[Col_I|Col_Is],Row_I,S3C,S3C,S3R) :-
	the_constraint5_aux_aux(Z_I,Col_I,Row_I,S3C,S3C,S3R),
	the_constraint5_aux(Z_I,Col_Is,Row_I,S3C,S3C,S3R).

the_constraint5_aux_aux(_,_,[],_,_,_).
the_constraint5_aux_aux(Z_I,Col_I,[Row_I|Row_Is],S3C,S3C,S3R) :-
	the_constraint5_aux_aux_aux(Z_I,Col_I,Row_I,S3C,S3C,S3R),
	the_constraint5_aux_aux(Z_I,Col_I,Row_Is,S3C,S3C,S3R).

the_constraint5_aux_aux_aux((Z_I,I), (Col_I,I), (Row_I,I), S3C, S3C, S3R) :- !,
	(0 =< I , I =< 27 ->
		write('\t'),
		write('I='), write(I), write(', '),
		write('I='), write(I), write(', '),
		write('I='), write(I), write(', '),
		nl,
		Z_I #= 3 #<=> (Col_I - 2 #=< S3C #/\ S3C #=<  Col_I #/\ S3R#= Row_I)
	;
		true
	).
the_constraint5_aux_aux_aux(_,_,_,_,_,_).

the_constraint6([],_,_,_,_,_).
the_constraint6([Z_I|Z_Is],Col_I,Row_I,S4C,S4C,S4R) :-
	the_constraint6_aux(Z_I,Col_I,Row_I,S4C,S4C,S4R),
	the_constraint6(Z_Is,Col_I,Row_I,S4C,S4C,S4R).

the_constraint6_aux(_,[],_,_,_,_).
the_constraint6_aux(Z_I,[Col_I|Col_Is],Row_I,S4C,S4C,S4R) :-
	the_constraint6_aux_aux(Z_I,Col_I,Row_I,S4C,S4C,S4R),
	the_constraint6_aux(Z_I,Col_Is,Row_I,S4C,S4C,S4R).

the_constraint6_aux_aux(_,_,[],_,_,_).
the_constraint6_aux_aux(Z_I,Col_I,[Row_I|Row_Is],S4C,S4C,S4R) :-
	the_constraint6_aux_aux_aux(Z_I,Col_I,Row_I,S4C,S4C,S4R),
	the_constraint6_aux_aux(Z_I,Col_I,Row_Is,S4C,S4C,S4R).

the_constraint6_aux_aux_aux((Z_I,I), (Col_I,I), (Row_I,I), S4C, S4C, S4R) :- !,
	(0 =< I , I =< 27 ->
		write('\t'),
		write('I='), write(I), write(', '),
		write('I='), write(I), write(', '),
		write('I='), write(I), write(', '),
		nl,
		Z_I #= 4 #<=> (Col_I - 4 #=< S4C #/\ S4C #=<  Col_I #/\ Row_I #= S4R)
	;
		true
	).
the_constraint6_aux_aux_aux(_,_,_,_,_,_).

