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
		write('[S2C,S2R,S3C,S3R,S4C,S4R,S5C,S5R,Z,Col,Row] = '), write(__S),
		nl,
		fail
	;
		write('=======================[ End Solutions ]======================='),
		nl,
		fail
	).

the_problem([S2C,S2R,S3C,S3R,S4C,S4R,S5C,S5R,Z,Col,Row]) :-
	S2C in 0..7,
	S2R in 0..5,
	S3C in 0..6,
	S3R in 0..4,
	S4C in 0..5,
	S4R in 0..3,
	S5C in 0..4,
	S5R in 0..2,
	length(Z,63),
	domain(Z,1,5),
	numbered_list(Z,ZL,0),
	length(Col,63),
	domain(Col,0,8),
	numbered_list(Col,ColL,0),
	length(Row,63),
	domain(Row,0,6),
	numbered_list(Row,RowL,0),
	all_constraints([S2C,S2R,S3C,S3R,S4C,S4R,S5C,S5R,ZL,ColL,RowL]),
	myappend([S2C,S2R,S3C,S3R,S4C,S4R,S5C,S5R],Z,__Tmp1),
	myappend(__Tmp1,Col,__Tmp2),
	myappend(__Tmp2,Row,__Tmp3),
	labeling([leftmost, step, up], __Tmp3).

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

all_constraints([S2C,S2R,S3C,S3R,S4C,S4R,S5C,S5R,Z,Col,Row]) :-
	the_constraint1(Z,Col,Row,S2C,S2C,S2R,S2R),
	the_constraint2(Z,Col,Row,S3C,S3C,S3R,S3R),
	the_constraint3(Z,Col,Row,S4C,S4C,S4R,S4R),
	the_constraint4(Z,Col,Row,S5C,S5C,S5R,S5R),
	the_constraint5(Col),
	the_constraint6(Row).

the_constraint1([],_,_,_,_,_,_).
the_constraint1([Z_I|Z_Is],Col_I,Row_I,S2C,S2C,S2R,S2R) :-
	the_constraint1_aux(Z_I,Col_I,Row_I,S2C,S2C,S2R,S2R),
	the_constraint1(Z_Is,Col_I,Row_I,S2C,S2C,S2R,S2R).

the_constraint1_aux(_,[],_,_,_,_,_).
the_constraint1_aux(Z_I,[Col_I|Col_Is],Row_I,S2C,S2C,S2R,S2R) :-
	the_constraint1_aux_aux(Z_I,Col_I,Row_I,S2C,S2C,S2R,S2R),
	the_constraint1_aux(Z_I,Col_Is,Row_I,S2C,S2C,S2R,S2R).

the_constraint1_aux_aux(_,_,[],_,_,_,_).
the_constraint1_aux_aux(Z_I,Col_I,[Row_I|Row_Is],S2C,S2C,S2R,S2R) :-
	the_constraint1_aux_aux_aux(Z_I,Col_I,Row_I,S2C,S2C,S2R,S2R),
	the_constraint1_aux_aux(Z_I,Col_I,Row_Is,S2C,S2C,S2R,S2R).

the_constraint1_aux_aux_aux((Z_I,I), (Col_I,I), (Row_I,I), S2C, S2C, S2R, S2R) :- !,
	(0 =< I , I=<62 ->
		Z_I #= 2 #<=> (Col_I - 1 #=< S2C #/\ S2C #=< Col_I #/\ Row_I - 1 #=< S2R #/\ S2R #=< Row_I) 
	;
		true
	).
the_constraint1_aux_aux_aux(_,_,_,_,_,_,_).

the_constraint2([],_,_,_,_,_,_).
the_constraint2([Z_I|Z_Is],Col_I,Row_I,S3C,S3C,S3R,S3R) :-
	the_constraint2_aux(Z_I,Col_I,Row_I,S3C,S3C,S3R,S3R),
	the_constraint2(Z_Is,Col_I,Row_I,S3C,S3C,S3R,S3R).

the_constraint2_aux(_,[],_,_,_,_,_).
the_constraint2_aux(Z_I,[Col_I|Col_Is],Row_I,S3C,S3C,S3R,S3R) :-
	the_constraint2_aux_aux(Z_I,Col_I,Row_I,S3C,S3C,S3R,S3R),
	the_constraint2_aux(Z_I,Col_Is,Row_I,S3C,S3C,S3R,S3R).

the_constraint2_aux_aux(_,_,[],_,_,_,_).
the_constraint2_aux_aux(Z_I,Col_I,[Row_I|Row_Is],S3C,S3C,S3R,S3R) :-
	the_constraint2_aux_aux_aux(Z_I,Col_I,Row_I,S3C,S3C,S3R,S3R),
	the_constraint2_aux_aux(Z_I,Col_I,Row_Is,S3C,S3C,S3R,S3R).

the_constraint2_aux_aux_aux((Z_I,I), (Col_I,I), (Row_I,I), S3C, S3C, S3R, S3R) :- !,
	(0 =< I , I=<62 ->
		Z_I #= 3 #<=> (Col_I - 2 #=< S3C #/\ S3C #=< Col_I #/\ Row_I - 2 #=< S3R #/\ S3R #=< Row_I) 
	;
		true
	).
the_constraint2_aux_aux_aux(_,_,_,_,_,_,_).

the_constraint3([],_,_,_,_,_,_).
the_constraint3([Z_I|Z_Is],Col_I,Row_I,S4C,S4C,S4R,S4R) :-
	the_constraint3_aux(Z_I,Col_I,Row_I,S4C,S4C,S4R,S4R),
	the_constraint3(Z_Is,Col_I,Row_I,S4C,S4C,S4R,S4R).

the_constraint3_aux(_,[],_,_,_,_,_).
the_constraint3_aux(Z_I,[Col_I|Col_Is],Row_I,S4C,S4C,S4R,S4R) :-
	the_constraint3_aux_aux(Z_I,Col_I,Row_I,S4C,S4C,S4R,S4R),
	the_constraint3_aux(Z_I,Col_Is,Row_I,S4C,S4C,S4R,S4R).

the_constraint3_aux_aux(_,_,[],_,_,_,_).
the_constraint3_aux_aux(Z_I,Col_I,[Row_I|Row_Is],S4C,S4C,S4R,S4R) :-
	the_constraint3_aux_aux_aux(Z_I,Col_I,Row_I,S4C,S4C,S4R,S4R),
	the_constraint3_aux_aux(Z_I,Col_I,Row_Is,S4C,S4C,S4R,S4R).

the_constraint3_aux_aux_aux((Z_I,I), (Col_I,I), (Row_I,I), S4C, S4C, S4R, S4R) :- !,
	(0 =< I , I=<62 ->
		Z_I #= 4 #<=> (Col_I - 3 #=< S4C #/\ S4C #=< Col_I #/\ Row_I - 3 #=< S4R #/\ S4R #=< Row_I) 
	;
		true
	).
the_constraint3_aux_aux_aux(_,_,_,_,_,_,_).

the_constraint4([],_,_,_,_,_,_).
the_constraint4([Z_I|Z_Is],Col_I,Row_I,S5C,S5C,S5R,S5R) :-
	the_constraint4_aux(Z_I,Col_I,Row_I,S5C,S5C,S5R,S5R),
	the_constraint4(Z_Is,Col_I,Row_I,S5C,S5C,S5R,S5R).

the_constraint4_aux(_,[],_,_,_,_,_).
the_constraint4_aux(Z_I,[Col_I|Col_Is],Row_I,S5C,S5C,S5R,S5R) :-
	the_constraint4_aux_aux(Z_I,Col_I,Row_I,S5C,S5C,S5R,S5R),
	the_constraint4_aux(Z_I,Col_Is,Row_I,S5C,S5C,S5R,S5R).

the_constraint4_aux_aux(_,_,[],_,_,_,_).
the_constraint4_aux_aux(Z_I,Col_I,[Row_I|Row_Is],S5C,S5C,S5R,S5R) :-
	the_constraint4_aux_aux_aux(Z_I,Col_I,Row_I,S5C,S5C,S5R,S5R),
	the_constraint4_aux_aux(Z_I,Col_I,Row_Is,S5C,S5C,S5R,S5R).

the_constraint4_aux_aux_aux((Z_I,I), (Col_I,I), (Row_I,I), S5C, S5C, S5R, S5R) :- !,
	(0 =< I , I=<62 ->
		Z_I #= 5 #<=> (Col_I - 4 #=< S5C #/\ S5C #=< Col_I #/\ Row_I - 4 #=< S5R #/\ S5R #=< Row_I) 
	;
		true
	).
the_constraint4_aux_aux_aux(_,_,_,_,_,_,_).

the_constraint5([]).
the_constraint5([Col_I|Col_Is]) :-
	the_constraint5_aux(Col_I),
	the_constraint5(Col_Is).

the_constraint5_aux((Col_I,I)) :- !,
	(0 =< I , I=<62 ->
		Col_I #= I mod 9 
	;
		true
	).
the_constraint5_aux(_).

the_constraint6([]).
the_constraint6([Row_I|Row_Is]) :-
	the_constraint6_aux(Row_I),
	the_constraint6(Row_Is).

the_constraint6_aux((Row_I,I)) :- !,
	(0 =< I , I=<62 ->
		Row_I #= ( I / 9 )
	;
		true
	).
the_constraint6_aux(_).

