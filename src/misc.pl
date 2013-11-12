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

place_targets(_, [], _, Tn, Tn).
place_targets(P, [(Ps, _)|Ts], N, Tn1, Tn3) :-
  N1 is N + 1,
  ( member(P, Ps) -> 
    format_atom('t_~p', [N], Tn),
    Tn2 = [Tn|Tn1]
  ; Tn2 = Tn1
  ),
  place_targets(P, Ts, N1, Tn2, Tn3).

targets_for_place(P, Tn) :-
  target(Ts),
  place_targets(P, Ts, 1, [], Tn).

traps_for_place(P, Tns) :-
  findall(Tn, (
    trap(N, Tr),
    member(P, Tr),
    format_atom('tr_~p', [N], Tn)
  ), Tns).
find_traps(Tns) :-
  findall(Tn, (
    trap(N, _),
    format_atom('tr_~p', [N], Tn)
  ), Tns).

