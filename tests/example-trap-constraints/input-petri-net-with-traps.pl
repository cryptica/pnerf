place('nc').
place('cs1').
place('cs2').
place('s1').
place('s2').
transition(t1, ['nc', 's1', 's2'], ['cs1', 's2']).
transition(t2, ['nc', 's1', 's2'], ['cs2', 's1']).
transition(t3, ['cs1'], ['nc', 's1']).
transition(t4, ['cs2'], ['nc', 's2']).
init('nc', 2).
init('s1', 1).
init('s2', 1).
target(1, [(['cs1','cs2'],2)]).
trap(trap_1, [s1,s2]).
