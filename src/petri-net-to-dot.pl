:- dynamic place/3.        % place(Id, InTransitions, OutTransitions).
:- dynamic transition/3.   % transition(Id, InPlaces, OutPlaces).
:- dynamic init/2.         % init(PlaceId, InitVal).
:- dynamic cond/1.         % cond(Z3Atom).

:- ['load-pl-file.pl'].

print_places :-
  findall( _ , (
    place(P, _, _),
    format('~p [label="~p', [P, P]),
    ( init(P, V) ->
      format('(~p)', [V])
    ; true
    ),
    print('"] ;\n')
  ), _ ).

print_transitions :-
  findall( _ , (
    transition(T, IPs, OPs),
    format('~p [label="~p", shape=box] ;\n', [T, T]),
    (  foreach(P, IPs)
    do format('~p -> ~p', [P, T]),
       (( weight(P, T, W), W > 1 ) ->
          format(' [label="~p"]', [W]) 
       ;  true
       ),
       print(';\n')
    ),
    (  foreach(P, OPs)
    do format('~p -> ~p', [T, P]),
       (( weight(T, P, W), W > 1 ) ->
          format(' [label="~p"]', [W]) 
       ;  true
       ),
       print(';\n')
    )
  ), _ ).

net_to_dot :-
  print('digraph petrinet {\n'),
  print('size="10,10"\n'),
  print_places,
  print_transitions,
  print('}\n').

:-
  prolog_flag(argv, Argv),
  (   foreach(F, Argv)
  do  load_pl_file(F)
  ),
  net_to_dot,
  halt.
