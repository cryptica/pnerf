:- dynamic place/3.        % place(Id, InTransitions, OutTransitions).
:- dynamic assignment/2.   % assignment(Variable, Value).
:- dynamic set_zero/1.     % set_zero(Place).

:- ['load-pl-file.pl'].
:- ['misc.pl'].

z3_constraints :-
        findall( _ , (
                       place(P, _, _),
                       assignment(P, 0),
                       format('(assert (= ~p 0))\n', [P])
                     ), _ ),
        set_zero(P1),
        format('(assert (= ~p 0))\n', [P1]).

% Entry point
:-      prolog_flag(argv, Argv),
        (   foreach(F, Argv)
        do  load_pl_file(F)
        ),
        z3_constraints,
        halt.
