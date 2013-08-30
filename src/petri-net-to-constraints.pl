:- dynamic place/3.        % place(Id, InTransitions, OutTransitions).
:- dynamic transition/3.   % transition(Id, InPlaces, OutPlaces).
:- dynamic init/1.         % init(PlaceId).
:- dynamic cond/1.         % cond(Z3Atom).

:- ['load-pl-file.pl'].

z3_vars :-
        findall( _ , (
                       place(P, _, _),
                       format('(declare-fun ~q () Int)\n', P)
                     ), _ ),
        findall( _ , (
                       transition(T, _, _),
                       format('(declare-fun ~q () Int)\n', T)
                     ), _ ).
z3_plus(L) :-
        (   foreach(X, L),
            count(_, 1, N)
        do  format('(+ ~q ', X)
        ),
        print(0),
        (   for(_, 1, N)
        do  print(')')
        ).
z3_place_eqs :-
        findall( _ , (
                       place(P, I, O),
                       (   init(P) ->
                           format('(assert (= ~q (+ 1 (- ', [P])
                       ;   format('(assert (= ~q (+ 0 (- ', [P])
                       ),
                       z3_plus(I),
                       print(' '),
                       z3_plus(O),
                       print('))))'),
                       nl
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