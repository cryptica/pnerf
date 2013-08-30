:- dynamic place/1.        % place(Id).
:- dynamic place/3.        % place(Id, InTransitions, OutTransitions).
:- dynamic transition/2.   % transition(InPlaces, OutPlaces).
:- dynamic transition/3.   % transition(Id, InPlaces, OutPlaces).
:- dynamic init/1.         % init(PlaceId).
:- dynamic cond/1.         % cond(Z3Atom).
:- dynamic trans_count/1.  % trans_count(NextTransSymbolId).

:- ['load-pl-file.pl'].

trans_count(0).
new_trans_sy(Sy) :-
        retract( trans_count(C) ),
        Cp is C + 1,
        number_chars(Cp, Nc),
        atom_chars(Sy, ['t'|Nc]),
        assert( trans_count(Cp) ).

label_transitions :-
        findall( _ , (
                       retract( transition(I, O) ),
                       new_trans_sy(Tsy),
                       assert( transition(Tsy, I, O) )
                     ), _ ).

connect_places_w_transitions :-
        findall( _ , (
                       retract( place(P) ),
                       assert( place(P, [], []) )
                     ), _ ),
        findall( _ , (
                       transition(T, Psi, Pso),
                       (   foreach(I, Psi)
                       do  retract( place(I, Ii, Io) ),
                           assert( place(I, Ii, [T|Io]) )
                       ),
                       (  foreach(O, Pso)
                       do  retract( place(O, Oi, Oo) ),
                           assert( place(O, [T|Oi], Oo) )
                       )
                     ), _ ).

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
        label_transitions,
        connect_places_w_transitions,
        z3_constraints,
        halt.