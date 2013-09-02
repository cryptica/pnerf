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

