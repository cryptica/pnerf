:- dynamic assignment/2. % assignment(Preimage, Image).

:- ['load-pl-file.pl'].
:- ['pretty-printing.pl'].

delta_condition :-
        findall(P, assignment(P, true), Ps),
        print('(assert (>= (+ '),
        print_seq(Ps),
        print(') 1))\n').

% Entry point
:-      prolog_flag(argv, Argv),
        (   foreach(F, Argv)
        do  load_pl_file(F)
        ),
        delta_condition,
        halt.
