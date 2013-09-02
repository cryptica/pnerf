:- dynamic place/3.        % place(Id, InTransitions, OutTransitions).
:- dynamic transition/3.   % transition(Id, InPlaces, OutPlaces).
:- dynamic init/1.         % init(PlaceId).
:- dynamic cond/1.         % cond(Z3Atom).

:- use_module(library(ordsets)).

:- ['load-pl-file.pl'].
:- ['pretty-printing.pl'].

z3_vars :-
        findall( _ , (
                       place(P, _, _),
                       format('(declare-fun ~q () Int)\n', P)
                     ), _ ),
        findall( _ , (
                       transition(T, _, _),
                       format('(declare-fun ~q () Int)\n', T)
                     ), _ ).
z3_place_eqs :-
        findall( _ , (
                       place(P, I, O),
                       (   init(P) ->
                           format('(assert (= ~q (+ 1', [P])
                       ;   format('(assert (= ~q (+ 0', [P])
                       ),
                       list_to_ord_set(I, ISet),
                       list_to_ord_set(O, OSet),
                       ord_subtract(ISet, OSet, RelISet),
                       ord_subtract(OSet, ISet, RelOSet),
                       ( RelISet = [_|_] -> print(' ') ; true ),
                       print_seq(RelISet),
                       ( RelOSet = [_|_] -> print(' ') ; true ),
                       format_seq('(- ~p)', RelOSet),
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
