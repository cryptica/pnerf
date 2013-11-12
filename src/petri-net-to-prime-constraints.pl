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
                       format('(declare-fun ~p () Int)\n', [P]),
                       format('(assert (>= ~p 0))\n', P)
                     ), _ ),
        findall( _ , (
                       target_conj(Target, _, _),
                       format('(declare-fun ~p () Int)\n', [Target]),
                       format('(assert (>= ~p 0))\n', Target)
                     ), _ ),
        findall( _ , (
                       trap(Trap, _),
                       format('(declare-fun ~p () Int)\n', [Trap]),
                       format('(assert (>= ~p 0))\n', [Trap])
                     ), _ ).

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
                          vars_for_place(P, Vars),
                          ( W = 0 -> true
                          ; W = 1 ->
                              print(' '),
                              format_sum('~p', Vars)
                          ; W = -1 ->
                              print(' (- '),
                              format_sum('~p', Vars),
                              print(')')
                          ;
                              format(' (* ~p ', [W]),
                              format_sum('~p', Vars),
                              print(')')
                          )
                       ),
                       print(')))\n')
                     ), _ ).

z3_token_eqs :-
        findall(P1, place(P1, _, _), Ps),
        list_to_ord_set(Ps, PSet),
        print('(assert (< (+ 0'),
        (  foreach(P, PSet)
        do ( init(P, V) -> true; V = 0 ),
           vars_for_place(P, Vars),
           ( V = 0 -> true
           ; V = 1 ->
               print(' '),
               format_sum('~p', Vars)
           ;   format(' (* ~p ', [V]),
               format_sum('~p', Vars),
               print(')')
           )
        ),
        print(') '),
        target_products(TargetProducts),
        trap_products(TrapProducts),
        append(TargetProducts, TrapProducts, VarProducts),
        format_sum('~p', VarProducts),
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
