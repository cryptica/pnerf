:- dynamic assignment/2.   % assignment(Preimage, Image).
:- dynamic place/3.        % place(Id, InTransitions, OutTransitions).
:- dynamic init/2.         % init(PlaceId, InitVal).
:- dynamic target/1.       % target(ListOfTargets).

:- use_module(library(lists)).
:- use_module(library(ordsets)).

:- ['load-pl-file.pl'].
:- ['misc.pl'].

format_y_component(P, Y) :-
        ( Y = 0 -> true
        ; Y = 1 -> format('~p', [P])
        ; Y = -1 -> format('-~p', [P])
        ; format('~p~p', [Y, P])
        ).

y_invariant :-
        findall( (P, Y) , (
                place(P, _, _),
                targets_for_place(P, Tn),
                maplist(assignment, [P|Tn], Ys),
                sumlist(Ys, Y),
                Y > 0
        ), Xs ),
        list_to_ord_set(Xs, Xord),
        (   Xord = [(P0, Y0)|Xord1] ->
            format_y_component(P0, Y0),
            (   foreach((P1, Y1), Xord1)
            do  print(' + '),
                format_y_component(P1, Y1)
            )
        ;   print('0')
        ),
        findall( S , (
                member((P, Y), Xs),
                ( init(P, M0) -> true; M0 = 0 ),
                S is Y * M0
        ), Ss ),
        sumlist(Ss, Ssum),
        format(' <= ~p\n', [Ssum]).

% Entry point
:-      prolog_flag(argv, Argv),
        (   foreach(F, Argv)
        do  load_pl_file(F)
        ),
        y_invariant,
        halt.

