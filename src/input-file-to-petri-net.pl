:- dynamic place/1.        % place(Id).
:- dynamic place/3.        % place(Id, InTransitions, OutTransitions).
:- dynamic transition/2.   % transition(InPlaces, OutPlaces).
:- dynamic transition/3.   % transition(Id, InPlaces, OutPlaces).
:- dynamic init/1.         % init(PlaceId).
:- dynamic init/2.         % init(PlaceId, InitVal).
:- dynamic cond/1.         % cond(Z3Atom).
:- dynamic trans_count/1.  % trans_count(NextTransSymbolId).

:- ['load-pl-file.pl'].

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

connect_places_w_transitions :-
        findall( _ , (
                       retract( place(P) ),
                       assert( place(P, [], []) )
                     ), _ ),
        findall( _ , (
                       transition(T, Psi, Pso),
                       (   foreach(I, Psi)
                       do  retract( place(I, Ii, Io) ),
                           assert( place(I, Ii, [T|Io]) )
                       ),
                       (  foreach(O, Pso)
                       do  retract( place(O, Oi, Oo) ),
                           assert( place(O, [T|Oi], Oo) )
                       )
                     ), _ ).

% Entry point
:-      prolog_flag(argv, Argv),
        (   foreach(F, Argv)
        do  load_pl_file(F)
        ),
        label_transitions,
        connect_places_w_transitions,
        listing(place/3),
        listing(transition/3),
        findall( _,
                 (   init(P),
                     portray_clause(init(P, 1))
                 ), _),
        listing(init/2),
        listing(cond/1),
        halt.