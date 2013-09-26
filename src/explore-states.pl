:- dynamic place/3.        % place(Id, InTransitions, OutTransitions).
:- dynamic transition/3.   % transition(Id, InPlaces, OutPlaces).
:- dynamic weight/3.       % weight(In, Out, Weight).
:- dynamic init/2.         % init(PlaceId, InitVal).
:- dynamic target/2.       % target(PlaceId, TargetVal).
:- dynamic cond/1.         % cond(Z3Atom).

:- use_module(library(queues)).
:- use_module(library(ordsets)).
:- use_module(library(lists)).
:- use_module(library(aggregate)).
:- use_module(library(process)).

:- ['load-pl-file.pl'].
:- ['misc.pl'].

unsafe(M):-
  forall(
    target(P, N),
    ( member(P-N2, M),
      ( integer(N2) ->
        N2 >= N
      ; true
      )
    )
  ).

safe(M) :-
  File = ('/tmp/pp-exp-petri-net.pl'),
  tell(File),
  listing(place/3),
  listing(transition/3),
  listing(weight/3),
  (  foreach(Pi-Ni, M)
  do format('init(~p, ~p).\n', [Pi, Ni])
  ),
  nl,
  listing(cond/1),
  told,
  process_create('./main', [file(File)], [process(Proc), stdout(null)]),
  process_wait(Proc, ExitStatus),
  ExitStatus = exit(0).

successor_marking(M, Msucc) :-
  transition(T, Pis, Pos),
  ( foreach(Pi, Pis),
    fromto(M, Min, Mout, M1),
    param(T)
    do member(Pi-N, Min),
     ( integer(N) ->
       weight(Pi, T, Wi),
       N >= Wi,
       Nnext is N - Wi,
       ord_del_element(Min, Pi-N, Mint),
       ( Nnext > 0 ->
         ord_add_element(Mint, Pi-Nnext, Mout)
       ; Mout = Mint
       )
     ; Mout = Min
     )
  ),
  (  foreach(Po, Pos),
     fromto(M1, Min2, Mout2, Msucc),
     param(T)
  do 
     ( member(Po-N2, Min2) ->
       true
     ; N2 = 0
     ),
     ( integer(N2) ->
       weight(T, Po, Wo),
       Nnext2 is N2 + Wo,
       ord_del_element(Min2, Po-N2, Mint2),
       ord_add_element(Mint2, Po-Nnext2, Mout2)
     ; Mout2 = Min2
     )
  ).

bfs(MaxDepth, MaxDepth, _, _, _, dontknow).
bfs(Depth, MaxDepth, [], [], _, safe) :-
  Depth < MaxDepth.
bfs(Depth, MaxDepth, [], [H|QueueNextLevel], Visited, Result) :-
  Depth < MaxDepth,
  NextDepth is Depth + 1,
  reverse([H|QueueNextLevel], QueueCurrentLevel),
  bfs(NextDepth, MaxDepth, QueueCurrentLevel, [], Visited, Result).
bfs(Depth, MaxDepth, [M|QueueTail], QueueNextLevel, Visited, Result) :-
  length(QueueTail, L1),
  length(QueueNextLevel, L2),
  length(Visited, L3),
  L4 is L1 + L2,
  format('bfs exploring ~p\n', [M]),
  format('exploration depth ~p\n', [Depth]),
  format('queue size ~p\n', [L4]),
  format('visited size ~p\n\n', [L3]),
  Depth < MaxDepth,
  ( unsafe(M) ->
    Result = unsafe
  ; safe(M) ->
    bfs(Depth, MaxDepth, QueueTail, QueueNextLevel, [M|Visited], Result)
  ; findall(Msucc, (
      successor_marking(M, Msucc),
      \+ member(Msucc, [M|QueueTail]),
      \+ member(Msucc, QueueNextLevel),
      \+ member(Msucc, Visited)
    ), Msuccs),
    rev_append(Msuccs, QueueNextLevel, QueueNextLevelWithSuccs),
    bfs(Depth, MaxDepth, QueueTail, QueueNextLevelWithSuccs, [M|Visited], Result)
  ).

test_net(N, R) :-
  findall(Pm , (
    init(P, V),
    Pm = P-V
  ), Ml),
  list_to_ord_set(Ml, M),
  print('starting bfs\n'),
  bfs(0, N, [M], [], [], R),
  format('ended bfs with ~p\n', R).

% Entry point
:-
  prolog_flag(argv, [ArgN|Argv]),
  (  foreach(F, Argv)
  do load_pl_file(F)
  ),
  atom_codes(ArgN, CodeN),
  number_codes(N, CodeN),
  test_net(N, R),
  ( R = safe ->
    halt(0)
  ; R = unsafe ->
    halt(1)
  ; R = dontknow ->
    halt(2)
  ).
