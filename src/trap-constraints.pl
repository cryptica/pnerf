:- dynamic assignment/2.   % assignment(Preimage, Image).
:- dynamic place/3.        % place(Id, InTransitions, OutTransitions).
:- dynamic transition/3.   % transition(Id, InPlaces, OutPlaces).
:- dynamic init/2.         % init(PlaceId, InitVal).
:- dynamic cond/1.         % cond(Z3Atom).

:- ['load-pl-file.pl'].
:- ['misc.pl'].

trap_conditions :-
        findall( _,
                 (
                   place(P, _, _),
                   format('(declare-fun ~p () Bool)\n', [P])
                 ), _ ),
        nl,
        findall( _,
                 (
                   transition(T, _, _),
                   format('(declare-fun o_~p () Bool)\n', [T])
                 ), _ ),
        nl,
        % 1. S is a trap
        findall( _,
                 (
                   place(P, _, Ts),
                   format('(assert (implies ~p ', [P]),
                   format_conjunct('o_~p', Ts),
                   print('))\n')
                 ), _ ),
        nl,
        findall( _,
                 (
                   transition(T, _, Ps),
                   format('(assert (implies o_~p ', [T]),
                   format_disjunct('~p', Ps),
                   print('))\n')
                 ), _ ),
        nl,
        % 2. An element of S is marked in the initial state
        findall(P, (   init(P, V),
                       (   integer(V) -> V>0
                       ;   assignment(V, Val), Val>0
                       )),
                Ps),
        print('(assert '),
        format_disjunct('~p', Ps),
        print(')\n'),
        nl,
        % 3. No element of S is marked in the model
        findall( _,
                 (
                   assignment(Place, N),
                   N > 0,
                   place(Place, _, _),
                   format('(assert (not ~p))\n', [Place])
                 ), _ ).

 % Entry point
 :-      prolog_flag(argv, Argv),
         (   foreach(F, Argv)
         do  load_pl_file(F)
         ),
         trap_conditions,
         nl,
         print('(check-sat)\n'),
         print('(get-model)\n'),
         halt.
