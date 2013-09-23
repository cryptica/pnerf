:- dynamic place/3.        % place(Id, InTransitions, OutTransitions).
:- dynamic transition/3.   % transition(Id, InPlaces, OutPlaces).
:- dynamic weight/3.       % weight(In, Out, Weight).
:- dynamic init/2.         % init(PlaceId, InitVal).
:- dynamic target/2.       % target(PlaceId, TargetVal).
:- dynamic cond/1.         % cond(Z3Atom).

:- use_module(library(avl)).
:- use_module(library(lists)).
:- use_module(library(aggregate)).
:- use_module(library(process)).

:- ['load-pl-file.pl'].
:- ['misc.pl'].

unsafe(M):-
  forall(
    target(P, N),
    ( avl_fetch(P, M, N2),
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
  avl_to_list(M, L),
  (  foreach(Pi-Ni, L)
  do format('init(~p, ~p).\n', [Pi, Ni])
  ),
  nl,
  listing(cond/1),
  told,
  process_create('./main', [file(File)], [process(Proc)]),
  process_wait(Proc, ExitStatus),
  ExitStatus = exit(0).

successor_marking(M, Msucc) :-
  transition(T, Pis, Pos),
  (  foreach(Pi, Pis),
     fromto(M, Min, Mout, M1),
     param(T)
  do avl_fetch(Pi, Min, N),
     ( integer(N) ->
       weight(Pi, T, Wi),
       N >= Wi,
       Nnext is N - Wi,
       ( Nnext = 0 ->
         avl_delete(Pi, Min, _, Mout)
       ; avl_store(Pi, Min, Nnext, Mout)
       )
     ; Mout = Min
     )
  ),
  (  foreach(Po, Pos),
     fromto(M1, Min2, Mout2, Msucc),
     param(T)
  do 
     ( avl_fetch(Po, Min2, N2) ->
       true
     ; N2 = 0
     ),
     ( integer(N2) ->
       weight(T, Po, Wo),
       Nnext2 is N2 + Wo,
       avl_store(Po, Min2, Nnext2, Mout2)
     ; Mout2 = Min2
     )
  ),
  avl_to_list(M, Ml),
  avl_to_list(Msucc, Msuccl),
  format('~p - ~p -> ~p\n', [Ml, T, Msuccl]).

initial_marking(M) :-
  findall(Pm , (
    init(P, V),
    Pm = P-V
  ), Ml),
  list_to_avl(Ml, M).

test_safety(M, N, R) :-
  ( unsafe(M) ->
    R = unsafe
  ; safe(M) ->
    R = safe
  ; N = 0 ->
    R = dontknow
  ; Nsucc is N - 1,
    ( successor_marking(M, Msucc),
      test_safety(Msucc, Nsucc, Rsucc),
      Rsucc \== safe ->
      R = Rsucc
    ; R = safe
    )
  ),
  avl_to_list(M, Ml),
  format('~p is ~p!\n', [Ml, R]).

test_net(N, R) :-
  initial_marking(M),
  test_safety(M, N, R).

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
  ; halt(2)
  ).
