:- dynamic assignment/2.   % assignment(Preimage, Image).
:- dynamic place/3.        % place(Id, InTransitions, OutTransitions).
:- dynamic transition/3.   % transition(Id, InPlaces, OutPlaces).
:- dynamic init/2.         % init(PlaceId, InitVal).
:- dynamic cond/1.         % cond(Z3Atom).

:- use_module(library(lists)).

:- ['load-pl-file.pl'].
:- ['misc.pl'].

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
                   format('(declare-fun o_~p () Bool)\n', [T]),
                   format('(declare-fun ~p () Int)\n', [T])
                 ), _ ),
        nl,
        % 1. S is a trap in the subnet
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
                   format('(assert (implies (and o_~p (> ~p 0)) ', [T, T]),
                   format_disjunct('~p', Ps),
                   print('))\n')
                 ), _ ),
        nl,
        % 2. S contains a place with an incoming transition in the subnet
        findall(P,
                (
                  place(P, Ts, _),
                  include(subnet_transition, Ts, TsSub),
                  TsSub = [_|_]
                ), Ps),
        print('(assert '),
        format_disjunct('~p', Ps),
        print(')\n'),
        nl,
        % 3. No element of S is marked in the model
        findall( _,
                 (
                   place(P, _, _),
                   assignment(P, N),
                   N > 0,
                   format('(assert (not ~p))\n', [P])
                 ), _ ),
        nl,
        % 4. Only used transitions are enabled
        findall( _,
                 (
                   transition(T, _, _),
                   assignment(T, N),
                   format('(assert (= ~p ~p))\n', [T, N])
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
