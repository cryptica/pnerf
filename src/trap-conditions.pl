:- dynamic assignment/2.   % assignment(Preimage, Image).
:- dynamic place/3.        % place(Id, InTransitions, OutTransitions).
:- dynamic transition/3.   % transition(Id, InPlaces, OutPlaces).
:- dynamic init/1.         % init(PlaceId).
:- dynamic cond/1.         % cond(Z3Atom).

:- ['load-pl-file.pl'].
:- ['pretty-printing.pl'].


place(p2, [u1], [u2,u3]).
transition(u2, [p2,hold2], [p3]).
transition(u3, [p2,hold1], []).

trap_conditions :-
        findall( _,
                 (
                   place(P, _, _),
                   format('(declare-fun ~p () Bool)\n', [P])
                 ), _ ),
        nl,
        % 1. S is a trap

 % place(p2, [u1], [u3,u2]).
 % transition(u2, [p2,hold2], [p3,hold1]).
 % transition(u3, [p2,hold1], [p3,hold1]).
 % ---------------------------------------
 % p2 -> (p3 | hold1) ^ (p3 | hold1)

 % place(p2, [u1], [u3]).
 % transition(u3, [p2,hold1], []).
 % ---------------------------------------
 % p2 -> (and false)

 % place(p2, [u1], [u2,u3]).
 % transition(u2, [p2,hold2], [p3]).
 % transition(u3, [p2,hold1], []).
 % ---------------------------------------
 % p2 -> (and (or p3) false)
 % A ^ true = A
 % A ^ false = false

         % findall( _,
         %          (
                    
         %          ), _ ),
         % nl,
        
         % 2. An element of S is marked in the initial state
         findall( P, init(P), Ps),
         (   Ps = [_|_] ->
             print('(assert (or '),
             print_seq(Ps),
             print(')\n')
         ;   true
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
         % print('(check-sat)\n'),
         % print('(get-model)\n').
         % print('NYI: trap conditions\n').

 % Entry point
 :-      prolog_flag(argv, Argv),
         (   foreach(F, Argv)
         do  load_pl_file(F)
         ),
         trap_conditions,
         print('(check-sat)\n'),
         print('(get-model)\n'),
         halt(1).
