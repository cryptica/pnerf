:- dynamic place/3.        % place(Id, InTransitions, OutTransitions).
:- dynamic assignment/2.   % assignment(Variable, Value).

:- ['load-pl-file.pl'].
:- ['misc.pl'].

minimization_constraints :-
        findall( _ , (
             place(P, _, _),
             format('(declare-fun b_~p () Int)\n', [P]),
             format('(assert (implies (> ~p 0) (= b_~p 1)))\n', [P, P]),
             format('(assert (implies (= ~p 0) (= b_~p 0)))\n', [P, P])
        ), _ ),
        findall(P, place(P, _, _), Ps),
        findall(P, (
             place(P, _, _),
             assignment(P, V),
             V > 0
        ), PsV),
        length(PsV, Count),
        print('(assert (< '),
        format_sum('b_~p', Ps),
        format(' ~p))', [Count]).

% Entry point
:-      prolog_flag(argv, Argv),
        (   foreach(F, Argv)
        do  load_pl_file(F)
        ),
        minimization_constraints,
        halt.
