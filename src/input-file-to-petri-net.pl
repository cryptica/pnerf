:- dynamic place/1.        % place(Id).
:- dynamic place/3.        % place(Id, InTransitions, OutTransitions).
:- dynamic transition/2.   % transition(InPlaces, OutPlaces).
:- dynamic transition/3.   % transition(Id, InPlaces, OutPlaces).
:- dynamic weight/3.       % weight(In, Out, Weight).
:- dynamic init/1.         % init(PlaceId).
:- dynamic init/2.         % init(PlaceId, InitVal).
:- dynamic cond/1.         % cond(Z3Atom).
:- dynamic target/2.       % target(TargetNum, ListOfTargets).
:- dynamic target/1.       % target(ListOfTargets).
:- dynamic trans_count/1.  % trans_count(NextTransSymbolId).

:- use_module(library(aggregate)).

:- ['load-pl-file.pl'].
:- ['misc.pl'].

trans_count(0).
new_trans_sy(Sy) :-
        retract( trans_count(C) ),
        Cp is C + 1,
        number_chars(Cp, Nc),
        atom_chars(Sy, ['t'|Nc]),
        assert( trans_count(Cp) ).

label_transitions :-
        findall( _ , (
                       retract( transition(I, O) ),
                       new_trans_sy(Tsy),
                       assert( transition(Tsy, I, O) )
                     ), _ ).

remove_weight(Pi, Po) :-
        (   Pi = (Po,_) ->
            true
        ;   Po = Pi
        ).

remove_weight_from_transitions :-
        findall( _ , (
                       retract( transition(Id, Iw, Ow) ),
                       maplist(remove_weight, Iw, I),
                       maplist(remove_weight, Ow, O),
                       assert( transition(Id, I, O) )
                     ), _ ).

connect_places_w_transitions :-
        findall( _ , (
                       retract( place(P) ),
                       assert( place(P, [], []) )
                     ), _ ),
        findall( _ , (
                       transition(T, Psi, Pso),
                       (   foreach(I, Psi)
                       do  (   I = (Ip, Iw) ->
                               retract( place(Ip, Ii, Io) ),
                               assert( place(Ip, Ii, [T|Io]) ),
                               assert( weight(Ip, T, Iw) )
                           ;   retract( place(I, Ii, Io) ),
                               assert( place(I, Ii, [T|Io]) ),
                               assert( weight(I, T, 1) )
                           )
                       ),
                       (  foreach(O, Pso)
                       do  (   O = (Op, Ow) ->
                               retract( place(Op, Oi, Oo) ),
                               assert( place(Op, [T|Oi], Oo) ),
                               assert( weight(T, Op, Ow) )
                           ;   retract( place(O, Oi, Oo) ),
                               assert( place(O, [T|Oi], Oo) ),
                               assert( weight(T, O, 1) )
                           )
                       )
                     ), _ ).
        
convert_targets(N) :-
  findall( _ , (
                 retract( target(N1, T) ),
                 ( ( N = 0; N = N1 ) ->
                   assert( target(T) )
                 )
               ), _ ).

% Entry point
:-      prolog_flag(argv, [TargetNumber|Argv]),
        (   foreach(F, Argv)
        do  load_pl_file(F)
        ),
        atom_codes(TargetNumber, Nc),
        number_codes(N,  Nc),
        ( ( N > 0, \+ target(N, _) ) ->
          format('Target ~p not available\n', [N]),
          halt(1)
        ; convert_targets(N)
        ),
        label_transitions,
        connect_places_w_transitions,
        remove_weight_from_transitions,
        listing(place/3),
        listing(transition/3),
        listing(weight/3),
        findall( _,
                 (   init(P),
                     portray_clause(init(P, 1))
                 ), _),
        listing(init/2),
        listing(cond/1),
        listing(target/1),
        halt.
