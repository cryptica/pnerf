:- dynamic place/3.        % place(Id, InTransitions, OutTransitions).
:- dynamic transition/3.   % transition(Id, InPlaces, OutPlaces).
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
                       format('(declare-fun ~q () Int)\n', V)
                     ), _ ),
        findall( _ , (
                       place(P, _, _),
                       format('(declare-fun ~q () Int)\n', P)
                     ), _ ),
        findall( _ , (
                       transition(T, _, _),
                       format('(declare-fun ~q () Int)\n', T)
                     ), _ ).
z3_transition_terms(T, Z3) :-
        (   T = (Tn, Tw) ->
            format_atom('(* ~p ~p)', [Tn,Tw], Z3)
        ;   Z3 = T
        ).
z3_place_eqs :-
        findall( _ , (
                       place(P, I, O),
                       (   init(P, V) ->
                           format('(assert (= ~q (+ ~p', [P, V])
                       ;   format('(assert (= ~q (+ 0', [P])
                       ),
                       list_to_ord_set(I, ISet),
                       list_to_ord_set(O, OSet),
                       ord_subtract(ISet, OSet, RelISet),
                       ord_subtract(OSet, ISet, RelOSet),
                       ( RelISet = [_|_] -> print(' ') ; true ),
                       maplist(z3_transition_terms, RelISet, RelITerms),
                       print_seq(RelITerms),
                       ( RelOSet = [_|_] -> print(' ') ; true ),
                       maplist(z3_transition_terms, RelOSet, RelOTerms),
                       format_seq('(- ~p)', RelOTerms),
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
