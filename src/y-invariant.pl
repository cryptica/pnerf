:- dynamic assignment/2.   % assignment(Preimage, Image).
:- dynamic place/3.        % place(Id, InTransitions, OutTransitions).
:- dynamic init/2.         % init(PlaceId, InitVal).
:- dynamic target/2.       % target(PlaceId, TargetVal).

:- use_module(library(lists)).
:- use_module(library(aggregate)).

:- ['load-pl-file.pl'].
:- ['misc.pl'].

y_invariant :-
        findall( S , (
                place(P, _, _),
                assignment(P, Y),
                (init(P, M0) -> true; M0 = 0 ),
                S is Y * M0
        ), Ss ),
        sumlist(Ss, Ssum),
        format('(assert (>= ~p (+', [Ssum]),
        findall( _ , (
                place(P, _, _),
                assignment(P, Y),
                target(P, B),
                B > 0,
                ( Y = 0 -> true
                ; Y = 1 -> format(' ~p', [P])
                ; Y = -1 -> format(' (- ~p)', [P])
                ; format(' (* ~p ~p)', [Y, P])
                )
        ), _ ),
        print(')))\n').

% Entry point
:-      prolog_flag(argv, Argv),
        (   foreach(F, Argv)
        do  load_pl_file(F)
        ),
        y_invariant,
        halt.

