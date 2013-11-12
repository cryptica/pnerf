:- dynamic assignment/2. % assignment(Preimage, Image).

:- ['../load-pl-file.pl'].
:- ['../misc.pl'].

delta_condition(N) :-
        findall(P, (
            place(P, _, _),
            assignment(P, true)
          ), Ps),
        portray_clause(trap(N, Ps)).

% Entry point
:-      prolog_flag(argv, [TrapNumber|Argv]),
        (   foreach(F, Argv)
        do  load_pl_file(F)
        ),
        atom_codes(TrapNumber, Nc),
        number_codes(N,  Nc),
        delta_condition(N),
        halt.
