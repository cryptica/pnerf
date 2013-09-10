:- use_module(library(lists)).
:- use_module(library(codesio)).

format_atom(Format, Arguments, Atom) :-
	format_to_codes(Format, Arguments, Codes),
	atom_codes(Atom, Codes).

map(F, Xs, Ys) :-
        same_length(Xs, Ys),
        (   foreach(X, Xs),
            foreach(Y, Ys),
            param(F)
        do  Goal =.. [F|[X,Y]],
            Goal
        ).        

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

