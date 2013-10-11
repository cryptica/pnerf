:- dynamic place/3.        % place(Id, InTransitions, OutTransitions).
:- dynamic transition/3.   % transition(Id, InPlaces, OutPlaces).
:- dynamic weight/3.       % weight(In, Out, Weight).
:- dynamic init/2.         % init(PlaceId, InitVal).
:- dynamic cond/1.         % cond(Z3Atom).

:- use_module(library(ordsets)).
:- use_module(library(lists)).

:- ['load-pl-file.pl'].
:- ['misc.pl'].

z3_vars :-
        findall( _ , (
                       init(_, V),
                       atom(V),
                       format('(declare-fun ~q () Real)\n', V)
                     ), _ ),
        findall( _ , (
                       place(P, _, _),
                       format('(declare-fun ~q () Real)\n', P)
                     ), _ ),
        findall( _ , (
                       transition(T, _, _),
                       format('(declare-fun ~q () Real)\n', T)
                     ), _ ).
z3_transition_terms(T, Z3) :-
        Z3 = T.
z3_place_eqs :-
        findall( _ , (
                       place(P, I, O),
                       (   init(P, V) ->
                           format('(assert (= ~q (+ ~p', [P, V])
                       ;   format('(assert (= ~q (+ 0', [P])
                       ),
                       list_to_ord_set(I, ISet),
                       list_to_ord_set(O, OSet),
                       ord_union(ISet, OSet, TSet),
                       %( TSet = [_|_] -> print(' ') ; true ),
                       (  foreach(T, TSet),
                          param(P)
                       do ( weight(P, T, Wo) -> true; Wo = 0 ),
                          ( weight(T, P, Wi) -> true; Wi = 0 ),
                          W is Wi - Wo,
                          ( W = 0 -> true
                          ; W = 1 -> format(' ~p', [T])
                          ; W = -1 -> format(' (- ~p)', [T])
                          ; format(' (* ~p ~p)', [W, T])
                          )
                       ),
                       %maplist(z3_transition_terms, TSet, TTerms),
                       %print_seq(TTerms),
                       print(')))\n')
                     ), _ ).
z3_nat_ineqs :-
        findall( _ , (
                       place(P, _, _),
                       format('(assert (>= ~q 0))\n', P)
                     ), _ ),
        findall( _ , (
                       transition(T, _, _),
                       format('(assert (>= ~q 0))\n', T)
                     ), _ ).
z3_conditions :-
        findall( _ , (
                       cond(C),
                       format('(assert ~p)\n', [C])
                     ), _ ).

z3_constraints :-
        z3_vars,
        z3_nat_ineqs,
        z3_place_eqs,
        z3_conditions,
        print('(check-sat)\n'),
        print('(get-model)\n').

% Entry point
:-      prolog_flag(argv, Argv),
        (   foreach(F, Argv)
        do  load_pl_file(F)
        ),
        z3_constraints,
        halt.
