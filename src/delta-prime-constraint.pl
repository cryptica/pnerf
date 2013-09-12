:- dynamic assignment/2. % assignment(Preimage, Image).
:- dynamic place/3.      % place(Id, InTransitions, OutTransitions).
:- dynamic transition/3. % transition(Id, InPlaces, OutPlaces).

:- use_module(library(lists)).

:- ['load-pl-file.pl'].
:- ['misc.pl'].

delta_prime_condition :-
        findall(TTerm, (
          transition(T, _, _),
          assignment(T, N),
          ( N > 0 -> 
            format_atom('(> ~p 0)', [T], TTerm)
          ; format_atom('(= ~p 0)', [T], TTerm)
          )
        ), Ts),
        findall(P, (
          place(P, _, _),
          assignment(P, true)
        ), Ps),
        print('(assert (implies (and '),
        print_seq(Ts),
        print(') (>= (+ '),
        print_seq(Ps),
        print(') 1)))\n').

% Entry point
:-      prolog_flag(argv, Argv),
        (   foreach(F, Argv)
        do  load_pl_file(F)
        ),
        delta_prime_condition,
        halt.
