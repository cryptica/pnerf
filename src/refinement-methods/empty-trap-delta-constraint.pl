:- dynamic assignment/2. % assignment(Preimage, Image).
:- dynamic place/3.      % place(Id, InTransitions, OutTransitions).
:- dynamic transition/3. % transition(Id, InPlaces, OutPlaces).

:- use_module(library(lists)).

:- ['../load-pl-file.pl'].
:- ['../misc.pl'].

delta_condition :-
        findall(T, (
          transition(T, _, _),
          format_atom('o_~p', [T], To),
          assignment(To, true)
        ), Tos),
        findall(T, (
          transition(T, _, _),
          format_atom('i_~p', [T], Ti),
          format_atom('o_~p', [T], To),
          assignment(Ti, true),
          assignment(To, false)
        ), Tis),
        print('(assert (implies '),
        format_disjunct('(> ~p 0)', Tos),
        print(' '),
        format_disjunct('(> ~p 0)', Tis),
        print('))\n').

% Entry point
:-      prolog_flag(argv, Argv),
        (   foreach(F, Argv)
        do  load_pl_file(F)
        ),
        delta_condition,
        halt.

