:- use_module(library(lists)).
:- use_module(library(codesio)).

format_atom(Format, Arguments, Atom) :-
	format_to_codes(Format, Arguments, Codes),
	atom_codes(Atom, Codes).

format_seq(F, Xs) :-
        (   Xs = [X1|Xs1] ->
            format(F, [X1]),
            (   foreach(X, Xs1),
                param(F)
            do  print(' '),
                format(F, [X])
            )
        ;   true
        ).

print_seq(Xs) :-
        format_seq('~p', Xs).

format_sum(F, Xs) :-
        (  Xs = [X] ->
           format(F, X)
        ;  Xs = [_,_|_] ->
           print('(+ '),
           format_seq(F, Xs),
           print(')')
        ;  print('0')
        ).

format_conjunct(F, Xs) :-
        (  Xs = [X] ->
           format(F, X)
        ;  Xs = [_,_|_] ->
           print('(and '),
           format_seq(F, Xs),
           print(')')
        ;  print('true')
        ).

format_disjunct(F, Xs) :-
        (  Xs = [X] ->
           format(F, X)
        ;  Xs = [_,_|_] ->
           print('(or '),
           format_seq(F, Xs),
           print(')')
        ;  print('false')
        ).

rev_append([], L2, L2).
rev_append([H|T], L2, [H|T2]) :-
  rev_append(T, L2, T2).

targets_for_place(P, Tns) :-
  findall(Tn, (
    target_conj(Tn, Ps, _),
    member(P, Ps)
  ), Tns).

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

traps_for_place(P, Tns) :-
  findall(Tn, (
    trap(Tn, Ps),
    member(P, Ps)
  ), Tns).
trap_products(Tns) :-
  findall(Tn, (
    trap(Trap, _),
    format_atom('~p', [Trap], Tn)
  ), Tns).

vars_for_place(P, Vars) :-
  targets_for_place(P, TargetNames),
  traps_for_place(P, TrapNames),
  append([P|TargetNames], TrapNames, Vars).
