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

print_conjunct(Xs) :-
        (  Xs = [X] ->
           format('~p', X)
        ;  Xs = [_,_|_] ->
           print('(and '),
           print_seq(Xs),
           print(')')
        ;  print('true')
        ).

print_disjunct(Xs) :-
        (  Xs = [X] ->
           format('~p', X)
        ;  Xs = [_,_|_] ->
           print('(or '),
           print_seq(Xs),
           print(')')
        ;  print('false')
        ).
