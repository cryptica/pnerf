:- dynamic place/3.        % place(Id, InTransitions, OutTransitions).
:- dynamic transition/3.   % transition(Id, InPlaces, OutPlaces).

:- use_module(library(aggregate)).

:- ['load-pl-file.pl'].
:- ['misc.pl'].

print_info :-
        findall(P, place(P, _, _), Ps),
        length(Ps, PlaceCount),
        findall(T, transition(T, _, _), Ts),
        length(Ts, TransitionCount),
        format('~d;~d;', [PlaceCount, TransitionCount]).

% Entry point
:-      prolog_flag(argv, Argv),
        (   foreach(F, Argv)
        do  load_pl_file(F)
        ),
        print_info,
        halt.
