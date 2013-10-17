place('s0').
place('s1').
place('s2').
place('s3').
place('s4').
place('s5').
place('s6').
place('s7').
place('s8').
place('s9').
place('s10').
place('s11').
place('l0').
place('l1').
place('l2').
place('l3').
place('l4').
place('l5').
transition(t1, ['l0', 's0'], ['s0', 'l1']).
transition(t2, ['l0', 's0'], ['s1', 'l1']).
transition(t3, ['l0', 's1'], ['s2', 'l2']).
transition(t4, ['l0', 's2'], ['s3', 'l3']).
transition(t5, ['l1', 's3'], ['s4', 'l4']).
transition(t6, ['l1', 's3'], ['s7', 'l5']).
transition(t7, ['l4', 's3'], ['s10', 'l1']).
transition(t8, ['l5', 's3'], ['s11', 'l1']).
transition(t9, ['l2', 's4'], ['s5', 'l0']).
transition(t10, ['l3', 's5'], ['s6', 'l0']).
transition(t11, ['l0', 's6'], ['s3', 'l2']).
transition(t12, ['l2', 's7'], ['s8', 'l0']).
transition(t13, ['l3', 's8'], ['s9', 'l0']).
transition(t14, ['l0', 's9'], ['s3', 'l3']).
transition(t15, ['l0', 's10'], ['s3', 'l3']).
transition(t16, ['l0', 's11'], ['s3', 'l2']).
init('l0', init1).
cond('(>= init1 1)').
init('s0', 1).
cond('(>= s3 1)').
target('s3', 1).
cond('(>= l1 1)').
target('l1', 1).
cond('(>= l3 1)').
target('l3', 1).
cond('(>= l4 2)').
target('l4', 2).
