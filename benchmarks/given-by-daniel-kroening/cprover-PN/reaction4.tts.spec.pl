place('s0').
place('s1').
place('s2').
place('s3').
place('s4').
place('s5').
place('s6').
place('s7').
place('l0').
place('l1').
place('l2').
place('l3').
place('l4').
place('l5').
place('l6').
place('l7').
transition(t1, ['l0', 's0'], ['s1', 'l1']).
transition(t2, ['l0', 's1'], ['s2', 'l7']).
transition(t3, ['l1', 's2'], ['s2', 'l4']).
transition(t4, ['l2', 's2'], ['s4', 'l5']).
transition(t5, ['l2', 's2'], ['s5', 'l3']).
transition(t6, ['l4', 's2'], ['s3', 'l1']).
transition(t7, ['l4', 's2'], ['s6', 'l1']).
transition(t8, ['l5', 's3'], ['s2', 'l2']).
transition(t9, ['l7', 's4'], ['s2', 'l6']).
transition(t10, ['l5', 's5'], ['s2', 'l0']).
transition(t11, ['l7', 's6'], ['s7', 'l2']).
transition(t12, ['l0', 's7'], ['s2', 'l5']).
init('l0', 1).
transition(init1, [], ['l0']).
init('s0', 1).
cond('(>= s2 1)').
target('s2', 1).
cond('(>= l7 2)').
target('l7', 2).
