:- dynamic assignment/2.   % assignment(Preimage, Image).
:- dynamic place/3.        % place(Id, InTransitions, OutTransitions).
:- dynamic transition/3.   % transition(Id, InPlaces, OutPlaces).
:- dynamic init/2.         % init(PlaceId, InitVal).
:- dynamic cond/1.         % cond(Z3Atom).

:- ['load-pl-file.pl'].
:- ['misc.pl'].

transition_successors(T) :-
        remove_weight(T, Tn),
        transition(Tn, _, OPs),
        (   OPs = [O] ->
            print(O)
        ;   OPs = [_|_] ->
            print('(or '),
            print_seq(OPs),
            print(')')
        ;   print(false)
        ).

 % place(p2, [u1], [u3]).
 % transition(u3, [p2,hold1], [p3]).
 % ---------------------------------------
 % p2 -> p3

 % place(p2, [u1], [u3]).
 % transition(u3, [p2,hold1], [p3, p4]).
 % ---------------------------------------
 % p2 -> (p3 | p4)

 % place(p2, [u1], [u3]).
 % transition(u3, [p2,hold1], []).
 % ---------------------------------------
 % p2 -> false

 % place(p2, [u1], [u2,u3]).
 % transition(u2, [p2,hold2], [p3]).
 % transition(u3, [p2,hold1], []).
 % ---------------------------------------
 % p2 -> p3 ^ false

 % place(p2, [u1], [u3,u2]).
 % transition(u2, [p2,hold2], [p3,hold1]).
 % transition(u3, [p2,hold1], [p3,hold1]).
 % ---------------------------------------
 % p2 -> (p3 | hold1) ^ (p3 | hold1)

trap_conditions :-
        findall( _,
                 (
                   place(P, _, _),
                   format('(declare-fun ~p () Bool)\n', [P])
                 ), _ ),
        nl,
        % 1. S is a trap
        findall( _,
                 (
                   place(P, _, Ts),
                   (   Ts = [T] ->
                       format('(assert (implies ~p ', [P]),
                       transition_successors(T),
                       print('))\n')
                   ;   Ts = [_|_] ->
                       format('(assert (implies ~p (and', [P]),
                       (   foreach(T, Ts)
                       do  print(' '),
                           transition_successors(T)
                       ),
                       print(')))\n')
                   ;   true
                   )
                 ), _ ),
        nl,
        % 2. An element of S is marked in the initial state
        findall(P, (   init(P, V),
                       (   integer(V) -> V>0
                       ;   assignment(V, Val), Val>0
                       )),
                Ps),
        (   Ps = [_|_] ->
            print('(assert (or '),
            print_seq(Ps),
            print('))\n')
        ;   print('(assert false)\n')
        ),
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
