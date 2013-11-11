place('nc').
place('cs1').
place('cs2').
place('s').
transition(t1, ['nc', 's'], ['cs1']).
transition(t2, ['nc', 's'], ['cs2']).
transition(t3, ['cs1'], ['nc', 's']).
transition(t4, ['cs2'], ['nc', 's']).
init('nc', 2).
init('s', 1).
target(1, [(['cs1','cs2'],2)]).
