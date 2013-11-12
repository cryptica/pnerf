:- dynamic assignment/2.   % assignment(Preimage, Image).
:- dynamic place/3.        % place(Id, InTransitions, OutTransitions).
:- dynamic init/2.         % init(PlaceId, InitVal).
:- dynamic target/1.       % target(ListOfTargets).
:- dynamic trap/2.         % trap(TrapNumber, ListOfPlaces).

:- use_module(library(lists)).
:- use_module(library(ordsets)).

:- ['load-pl-file.pl'].
:- ['misc.pl'].

format_y_component((P, Y), YTerm) :-
        ( Y = 1 ->
          format_atom('~p', [P], YTerm)
        ; Y > 0 ->
          format_atom('(* ~p ~p)', [Y, P], YTerm)
        ).

y_invariant :-
        findall( (P, Y) , (
                place(P, _, _),
                targets_for_place(P, TargetNames),
                traps_for_place(P, TrapNames),
                append([P|TargetNames], TrapNames, Vars),
                maplist(assignment, Vars, Ys),
                sumlist(Ys, Y),
                Y > 0
        ), Xs ),
        list_to_ord_set(Xs, Xord),
        findall( S , (
                member((P, Y), Xs),
                ( init(P, M0) -> true; M0 = 0 ),
                S is Y * M0
        ), Ss ),
        sumlist(Ss, Ssum),
        print('(assert (<= '),
        maplist(format_y_component, Xord, XordTerms),
        format_sum('~p', XordTerms),
        format(' ~p))\n', [Ssum]).

% Entry point
:-      prolog_flag(argv, Argv),
        (   foreach(F, Argv)
        do  load_pl_file(F)
        ),
        y_invariant,
        halt.

