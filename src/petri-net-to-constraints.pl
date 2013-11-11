:- dynamic place/3.        % place(Id, InTransitions, OutTransitions).
:- dynamic transition/3.   % transition(Id, InPlaces, OutPlaces).
:- dynamic weight/3.       % weight(In, Out, Weight).
:- dynamic init/2.         % init(PlaceId, InitVal).
:- dynamic target/1.       % target(ListOfTargets).

:- use_module(library(ordsets)).
:- use_module(library(lists)).

:- ['load-pl-file.pl'].
:- ['misc.pl'].

z3_vars(EquationType) :-
        findall( _ , (
                       init(_, V),
                       atom(V),
                       format('(declare-fun ~p () ~p)\n', [V, EquationType])
                     ), _ ),
        findall( _ , (
                       place(P, _, _),
                       format('(declare-fun ~p () ~p)\n', [P, EquationType])
                     ), _ ),
        findall( _ , (
                       transition(T, _, _),
                       format('(declare-fun ~p () ~p)\n', [T, EquationType])
                     ), _ ).
z3_place_eqs :-
        findall( _ , (
                       place(P, I, O),
                       (   init(P, V) ->
                           format('(assert (= ~p (+ ~p', [P, V])
                       ;   format('(assert (= ~p (+ 0', [P])
                       ),
                       list_to_ord_set(I, ISet),
                       list_to_ord_set(O, OSet),
                       ord_union(ISet, OSet, TSet),
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
                       print(')))\n')
                     ), _ ).
z3_nat_ineqs :-
        findall( _ , (
                       place(P, _, _),
                       format('(assert (>= ~p 0))\n', P)
                     ), _ ),
        findall( _ , (
                       transition(T, _, _),
                       format('(assert (>= ~p 0))\n', T)
                     ), _ ).

target_to_z3((Ps, V)) :-
        print('(>= '),
        format_sum('~p', Ps),
        format(' ~p)', [V]).
                  
z3_conditions :-
        print('(assert (or'),
        findall( _ , (
                       target(Ts),
                       print(' '),
                       (  Ts = [T] ->
                          target_to_z3(T)
                       ;  Ts = [T1|Ts1] ->
                          print('(and '),
                          target_to_z3(T1),
                          (   foreach(T2, Ts1 )
                          do  print(' '),
                              target_to_z3(T2)
                          ),
                          print(')')
                       ;  print('true')
                       )
                     ), _ ),
        print('))\n').

z3_constraints(EquationType) :-
        z3_vars(EquationType),
        z3_nat_ineqs,
        z3_place_eqs,
        z3_conditions,
        print('(check-sat)\n'),
        print('(get-model)\n').

% Entry point
:-      prolog_flag(argv, [EquationType|Argv]),
        (   foreach(F, Argv)
        do  load_pl_file(F)
        ),
        z3_constraints(EquationType),
        halt.
