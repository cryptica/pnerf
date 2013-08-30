:- dynamic assignment/2. % assignment(Preimage, Image).

:- ['load-pl-file.pl'].

delta_condition :-
        print('NYI: delta condition\n').

% Entry point
:-      prolog_flag(argv, Argv),
        (   foreach(F, Argv)
        do  load_pl_file(F)
        ),
        delta_condition,
        halt(1).
