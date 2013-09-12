:- dynamic assignment/2.   % assignment(Preimage, Image).
:- dynamic place/3.        % place(Id, InTransitions, OutTransitions).
:- dynamic transition/3.   % transition(Id, InPlaces, OutPlaces).
:- dynamic init/2.         % init(PlaceId, InitVal).
:- dynamic cond/1.         % cond(Z3Atom).

:- use_module(library(lists)).

:- ['load-pl-file.pl'].
:- ['misc.pl'].

%transition_successors(T) :-
  %        remove_weight(T, Tn),
  %        transition(Tn, _, OPs),
  %      (   OPs = [O] ->
  %          print(O)
  %      ;   OPs = [_|_] ->
  %          print('(or '),
  %          print_seq(OPs),
  %          print(')')
  %      ;   print(false)
  %      ).

subnet_transition(T) :-
        remove_weight(Elem, T),
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
                   format('(declare-fun b_~p () Bool)\n', [T]),
                   format('(declare-fun ~p () Int)\n', [T])
                 ), _ ),
        nl,
        % 1. S is a trap in the subnet
        findall( _,
                 (
                   place(P, _, Ts),
                   maplist(remove_weight, Ts, Tns),
                   (   Tns = [T] ->
                       format('(assert (implies ~p b_~p))\n', [P, T])
                   ;   Tns = [_|_] ->
                       format('(assert (implies ~p (and ', [P]),
                       format_seq('b_~p', Tns),
                       print(')))\n')
                   ;   true
                   )
                 ), _ ),
        nl,
        findall( _,
                 (
                   transition(T, _, Ps),
                   format('(assert (= b_~p (implies (> ~p 0) ', [T, T]),
                   (   Ps = [P] ->
                       format('~p', [P])
                   ;   Ps = [_|_] ->
                       print('(or '),
                       print_seq(Ps),
                       print(')')
                   ;   print('false')
                   ),
                   print(')))\n')
                 ), _ ),
        nl,
        % 2. S contains a place with an incoming transition in the subnet
        findall(P,
                (
                  place(P, Ts, _),
                  maplist(remove_weight, Ts, Tns),
                  include(subnet_transition, Ts, TsSub),
                  TsSub = [_|_]
                ), Ps),
        (   Ps = [_|_] ->
            print('(assert (or '),
            print_seq(Ps),
            print('))\n')
        ;   true
        ),
        nl,
        % 3. No element of S is marked in the model
        findall( _,
                 (
                   place(Place, _, _),
                   assignment(Place, N),
                   N > 0,
                   format('(assert (not ~p))\n', [Place])
                 ), _ ),
        nl,
        % 4. Only used transitions are enabled
        findall( _,
                 (
                   transition(Transition, _, _),
                   assignment(Transition, N),
                   format('(assert (= ~p ~p))\n', [Transition, N])
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
