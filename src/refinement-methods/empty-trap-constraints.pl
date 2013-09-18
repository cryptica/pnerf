:- dynamic assignment/2.   % assignment(Preimage, Image).
:- dynamic place/3.        % place(Id, InTransitions, OutTransitions).
:- dynamic transition/3.   % transition(Id, InPlaces, OutPlaces).
:- dynamic init/2.         % init(PlaceId, InitVal).
:- dynamic cond/1.         % cond(Z3Atom).

:- use_module(library(lists)).

:- ['../load-pl-file.pl'].
:- ['../misc.pl'].

subnet_transition(T) :-
        assignment(T, N),
        N > 0.

trap_conditions :-
        findall( _,
                 (
                   place(P, _, _),
                   format('(declare-fun ~p () Bool)\n', [P])
                 ), _ ),
        findall( _,
                 (
                   transition(T, _, _),
                   format('(declare-fun i_~p () Bool)\n', [T]),
                   format('(declare-fun o_~p () Bool)\n', [T])
                 ), _ ),
        nl,
        % 1. S is a trap with corresponding input and output transitions
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
                   place(P, Ts, _),
                   format('(assert (implies ~p ', [P]),
                   format_conjunct('i_~p', Ts),
                   print('))\n')
                 ), _ ),
        nl,
        findall( _,
                 (
                   transition(T, _, Ps),
                   format('(assert (implies o_~p i_~p))\n', [T, T])
                 ), _ ),
        nl,
        findall( _,
                 (
                   transition(T, _, Ps),
                   format('(assert (implies i_~p ', [T]),
                   format_disjunct('~p', Ps),
                   print('))\n')
                 ), _ ),
        nl,
        findall( _,
                 (
                   transition(T, Ps, _),
                   format('(assert (implies o_~p ', [T]),
                   format_disjunct('~p', Ps),
                   print('))\n')
                 ), _ ),
        nl,
        % 2. S is initially unmarked
        findall( _,
                 (
                   init(P, V),
                   (   integer(V) -> V>0
                   ;   assignment(V, Val), Val>0
                   ),
                   format('(assert (not ~p))\n', [P])
                 ), _ ),
        nl,
        % 3. One of the outgoing transitions of S is fired
        findall( T,
                 (
                   transition(T, _, _),
                   assignment(T, N),
                   N > 0
                 ), Ts ),
        print('(assert '),
        format_disjunct('o_~p', Ts),
        print(')\n'),
        nl,
        % 4. None of the incoming, but not outgoing transitions are fired
        findall( _,
                 (
                   transition(T, _, _),
                   assignment(T, N),
                   N > 0,
                   format('(assert (or o_~p (not i_~p)))\n', [T, T])
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

