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
place('l6').
place('l7').
place('l8').
place('l9').
transition(t1, ['l0', 's0'], ['s1', 'l5']).
transition(t2, ['l0', 's1'], ['s2', 'l6']).
transition(t3, ['l0', 's2'], ['s3', 'l7']).
transition(t4, ['l0', 's3'], ['s4', 'l7']).
transition(t5, ['l0', 's4'], ['s5', 'l7']).
transition(t6, ['l0', 's5'], ['s6', 'l7']).
transition(t7, ['l0', 's6'], ['s7', 'l7']).
transition(t8, ['l0', 's7'], ['s8', 'l7']).
transition(t9, ['l2', 's8'], ['s9', 'l9']).
transition(t10, ['l3', 's8'], ['s10', 'l1']).
transition(t11, ['l5', 's8'], ['s8', 'l8']).
transition(t12, ['l6', 's8'], ['s8', 'l2']).
transition(t13, ['l7', 's8'], ['s8', 'l3']).
transition(t14, ['l8', 's8'], ['s11', 'l4']).
transition(t15, ['l4', 's9'], ['s8', 'l0']).
transition(t16, ['l9', 's10'], ['s8', 'l6']).
transition(t17, ['l0', 's11'], ['s8', 'l5']).
init('l0', init1).
cond('(>= init1 1)').
init('s0', 1).
cond('(>= s8 1)').
target('s8', 1).
cond('(>= l9 2)').
target('l9', 2).
