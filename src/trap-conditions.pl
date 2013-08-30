:- dynamic assignment/2. % assignment(Preimage, Image).

:- ['load-pl-file.pl'].

trap_conditions :-
        print('NYI: trap conditions\n').

% Entry point
:-      prolog_flag(argv, Argv),
        (   foreach(F, Argv)
        do  load_pl_file(F)
        ),
        trap_conditions,
        halt(1).
