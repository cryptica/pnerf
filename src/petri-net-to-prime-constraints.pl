:- dynamic place/3.        % place(Id, InTransitions, OutTransitions).
:- dynamic transition/3.   % transition(Id, InPlaces, OutPlaces).
:- dynamic weight/3.       % weight(In, Out, Weight).
:- dynamic init/2.         % init(PlaceId, InitVal).
:- dynamic target/2.       % target(PlaceId, TargetVal).

:- use_module(library(ordsets)).
:- use_module(library(lists)).
:- use_module(library(aggregate)).

:- ['load-pl-file.pl'].
:- ['misc.pl'].

z3_vars :-
        findall( _ , (
                       place(P, _, _),
                       format('(declare-fun ~p () Real)\n', [P])
                     ), _ ).

z3_incidence_ineqs :-
        findall( _ , (
                       transition(T, I, O),
                       print('(assert (>= 0 (+'),
                       list_to_ord_set(I, ISet),
                       list_to_ord_set(O, OSet),
                       ord_union(ISet, OSet, PSet),
                       (  foreach(P, PSet),
                          param(T)
                       do ( weight(P, T, Wo) -> true; Wo = 0 ),
                          ( weight(T, P, Wi) -> true; Wi = 0 ),
                          W is Wi - Wo,
                          ( W = 0 -> true
                          ; W = 1 -> format(' ~p', [P])
                          ; W = -1 -> format(' (- ~p)', [P])
                          ; format(' (* ~p ~p)', [W, P])
                          )
                       ),
                       print(')))\n')
                     ), _ ).

z3_token_eqs :-
        print('(assert (= 1 (+ 0'),
        findall( _ , (
                       place(P, _, _),
                       ( aggregate(max(B), target(P, B), Bmax) ->
                         true
                       ; Bmax = 0
                       ),
                       (init(P, M0) -> true; M0 = 0 ),
                       W is Bmax - M0,
                       ( W = 0 -> true
                       ; W = 1 -> format(' ~p', [P])
                       ; W = -1 -> format(' (- ~p)', [P])
                       ; format(' (* ~p ~p)', [W, P])
                       )
                     ), _ ),
        print(')))\n').

z3_nonneg_ineqs :-
        findall( _ , (
                       place(P, _, _),
                       format('(assert (>= ~p 0))\n', P)
                     ), _ ).

z3_constraints :-
        z3_vars,
        z3_incidence_ineqs,
        z3_token_eqs,
        z3_nonneg_ineqs,
        print('(check-sat)\n'),
        print('(get-model)\n').

% Entry point
:-      prolog_flag(argv, Argv),
        (   foreach(F, Argv)
        do  load_pl_file(F)
        ),
        z3_constraints,
        halt.
