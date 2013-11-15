:- dynamic place/3.        % place(Id, InTransitions, OutTransitions).
:- dynamic transition/3.   % transition(Id, InPlaces, OutPlaces).
:- dynamic weight/3.       % weight(In, Out, Weight).
:- dynamic init/2.         % init(PlaceId, InitVal).
:- dynamic target_conj/3.  % target_conj(TargetName, ListOfPlaces, Number).
:- dynamic trap/2.         % trap(TrapName, ListOfPlaces).

:- use_module(library(ordsets)).
:- use_module(library(lists)).

:- ['load-pl-file.pl'].
:- ['misc.pl'].

z3_vars :-
        findall( _ , (
                       place(P, _, _),
                       format('(declare-fun ~p () Int)\n', [P])
                     ), _ ),
        findall( _ , (
                       target_conj(Target, _, _),
                       format('(declare-fun ~p () Int)\n', [Target])
                     ), _ ),
        findall( _ , (
                       trap(Trap, _),
                       format('(declare-fun ~p () Int)\n', [Trap])
                     ), _ ).

z3_inductive_ineqs :-
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
                          ( W = 0 -> true
                          ; W = 1 ->
                              format(' ~p', [P])
                          ; W = -1 ->
                              format(' (- ~p)', [P])
                          ;
                              format(' (* ~p ~p)', [W, P])
                          )
                       ),
                       print(')))\n')
                     ), _ ).

target_products(Tns) :-
  findall(Tn, (
    target_conj(Target, _, B),
    ( B = 0 ->
      Tn = '0'
    ; B = 1 ->
      format_atom('~p', [Target], Tn)
    ; B = -1 ->
      format_atom('(- ~p)', [Target], Tn)
    ; format_atom('(* ~p ~p)', [B, Target], Tn)
    )
  ), Tns).
trap_products(Tns) :-
  findall(Tn, (
    trap(Trap, _),
    format_atom('~p', [Trap], Tn)
  ), Tns).

z3_safety_ineq :-
        print('(assert (< (+ 0'),
        findall( _ , (
            init(P, V),
            V > 0,
            ( V = 1 ->
                format(' ~p', [P])
            ;   format(' (* ~p ~p)', [V, P])
            )
        ), _ ),
        print(') '),
        target_products(TargetProducts),
        trap_products(TrapProducts),
        append(TargetProducts, TrapProducts, VarProducts),
        format_sum('~p', VarProducts),
        print('))\n').

targets_for_place(P, Tns) :-
  findall(Tn, (
    target_conj(Tn, Ps, _),
    member(P, Ps)
  ), Tns).

traps_for_place(P, Tns) :-
  findall(Tn, (
    trap(Tn, Ps),
    member(P, Ps)
  ), Tns).

vars_for_place(P, Vars) :-
  targets_for_place(P, TargetNames),
  traps_for_place(P, TrapNames),
  append(TargetNames, TrapNames, Vars).

z3_property_ineqs :-
        findall( _ , (
            place(P, _, _),
            vars_for_place(P, Vars),
            format('(assert (>= ~p ', [P]),
            format_sum('~p', Vars),
            print('))\n')
        ), _ ).

z3_nat_ineqs :-
        findall( _ , (
                       target_conj(Target, _, _),
                       format('(assert (>= ~p 0))\n', Target)
                     ), _ ),
        findall( _ , (
                       trap(Trap, _),
                       format('(assert (>= ~p 0))\n', [Trap])
                     ), _ ).

z3_constraints :-
        z3_vars,
        z3_inductive_ineqs,
        z3_safety_ineq,
        z3_property_ineqs,
        z3_nat_ineqs,
        print('(check-sat)\n'),
        print('(get-model)\n').

% Entry point
:-      prolog_flag(argv, Argv),
        (   foreach(F, Argv)
        do  load_pl_file(F)
        ),
        z3_constraints,
        halt.
