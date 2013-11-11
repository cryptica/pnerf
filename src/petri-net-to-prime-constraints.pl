:- dynamic place/3.        % place(Id, InTransitions, OutTransitions).
:- dynamic transition/3.   % transition(Id, InPlaces, OutPlaces).
:- dynamic weight/3.       % weight(In, Out, Weight).
:- dynamic init/2.         % init(PlaceId, InitVal).
:- dynamic target/1.       % target(ListOfTargets).

:- use_module(library(ordsets)).
:- use_module(library(lists)).

:- ['load-pl-file.pl'].
:- ['misc.pl'].

target_vars([], _).
target_vars([_|Ts], N) :-
  N1 is N + 1,
  format('(declare-fun t_~p () Int)\n', [N]),
  format('(assert (>= t_~p 0))\n', N),
  target_vars(Ts, N1).

z3_vars :-
        findall( _ , (
                       place(P, _, _),
                       format('(declare-fun ~p () Int)\n', [P]),
                       format('(assert (>= ~p 0))\n', P)
                     ), _ ),
        target(Ts),
        target_vars(Ts, 1).

z3_incidence_ineqs :-
        findall( _ , (
                       transition(T, I, O),
                       print('(assert (>= 0 (+ 0'),
                       list_to_ord_set(I, ISet),
                       list_to_ord_set(O, OSet),
                       ord_union(ISet, OSet, PSet),
                       (  foreach(P, PSet),
                          param(T)
                       do ( weight(P, T, Wo) -> true; Wo = 0 ),
                          ( weight(T, P, Wi) -> true; Wi = 0 ),
                          W is Wi - Wo,
                          targets_for_place(P, Tn),
                          ( W = 0 -> true
                          ; W = 1 ->
                              print(' '),
                              format_sum('~p', [P|Tn])
                          ; W = -1 ->
                              print(' (- '),
                              format_sum('~p', [P|Tn]),
                              print(')')
                          ;
                              format(' (* ~p ', [W]),
                              format_sum('~p', [P|Tn]),
                              print(')')
                          )
                       ),
                       print(')))\n')
                     ), _ ).

target_products([], _, Tn, Tn).
target_products([(_, B)|Ts], N, Tn1, Tn2) :-
  ( B = 0 ->
      Tn = '0'
  ; B = 1 ->
      format_atom('t_~p', [N], Tn)
  ;   format_atom('(* ~p t_~p)', [B, N], Tn)
  ),
  N1 is N + 1,
  target_products(Ts, N1, [Tn|Tn1], Tn2).

z3_token_eqs :-
        findall(P1, place(P1, _, _), Ps),
        list_to_ord_set(Ps, PSet),
        print('(assert (< (+ 0'),
        (  foreach(P, PSet)
        do ( init(P, V) -> true; V = 0 ),
           targets_for_place(P, Tn),
           ( V = 0 -> true
           ; V = 1 ->
               print(' '),
               format_sum('~p', [P|Tn])
           ;   format(' (* ~p ', [V]),
               format_sum('~p', [P|Tn]),
               print(')')
           )
        ),
        print(') '),
        target(Ts),
        target_products(Ts, 1, [], Tn1),
        format_sum('~p', Tn1),
        print('))\n').

z3_constraints :-
        z3_vars,
        z3_incidence_ineqs,
        z3_token_eqs,
        print('(check-sat)\n'),
        print('(get-model)\n').

% Entry point
:-      prolog_flag(argv, Argv),
        (   foreach(F, Argv)
        do  load_pl_file(F)
        ),
        z3_constraints,
        halt.
