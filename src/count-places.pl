:- dynamic trap/2.         % trap(TrapName, ListOfPlaces).
:- dynamic place/3.        % place(Id, InTransitions, OutTransitions).
:- dynamic assignment/2.   % assignment(Preimage, Image).

:- use_module(library(aggregate)).

:- ['load-pl-file.pl'].
:- ['misc.pl'].

count_trap_places :-
        aggregate(sum(Pc), (
            trap(_, Ps),
            length(Ps, Pc)
        ), NumPlaces),
        format('~d', NumPlaces).

count_invariant_places :-
        findall( (P, Y) , (
                place(P, _, _),
                assignment(P, Y),
                Y > 0
        ), Xs ),
        length(Xs, NumPlaces),
        format('~d', NumPlaces).

% Entry point
:-      prolog_flag(argv, [Type|Argv]),
        (   foreach(F, Argv)
        do  load_pl_file(F)
        ),
        ( Type = 'trap' ->
          count_trap_places
        ; Type = 'invariant' ->
          count_invariant_places
        ; format('Invalid type: ~s', Type),
          halt(1)
        ),
        halt.

