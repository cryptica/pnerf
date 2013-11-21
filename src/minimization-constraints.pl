:- dynamic place/3.        % place(Id, InTransitions, OutTransitions).
:- dynamic assignment/2.   % assignment(Variable, Value).
:- dynamic set_zero/1.     % set_zero(Place).

:- ['load-pl-file.pl'].
:- ['misc.pl'].

next_constraint :-
        place(P, _, _),
        assignment(P, V),
        V > 0,
        \+ set_zero(P),
        portray_clause(set_zero(P)).

% Entry point
:-      prolog_flag(argv, Argv),
        (   foreach(F, Argv)
        do  load_pl_file(F)
        ),
        ( next_constraint ->
          halt(0)
        ; halt(1)
        ).
