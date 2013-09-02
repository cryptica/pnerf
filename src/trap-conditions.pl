:- dynamic assignment/2. % assignment(Preimage, Image).

:- ['load-pl-file.pl'].

%seq(Xs) :-
%        (   Xs = [X1|Xs1] ->
%            format('~p', [X1
%            (   foreach(X, Xs1)
%            do  format(' ~p', [X])
%            )
%        ;   true
%        ).

trap_conditions :-
        % 1. S is a trap
        % 2. An element of S is marked in the initial state
%        findall( Place, init(Place), InitiallyMarked ),
%        print('(assert (or '),
%        seq(Initiall
%        format('(assert ~p)\n', [InitiallyMarked]),
        % 3. No element of S is marked in the model
        findall( _,
                 (
                   assignment(Place, 0),
                   place(Place, _, _),
                   format('(assert (not ~p))\n', [Place])
                 ),
                 _ ).
        % print('(check-sat)\n'),
        % print('(get-model)\n').
        % print('NYI: trap conditions\n').

% Entry point
:-      prolog_flag(argv, Argv),
        (   foreach(F, Argv)
        do  load_pl_file(F)
        ),
        trap_conditions,
        halt(1).
