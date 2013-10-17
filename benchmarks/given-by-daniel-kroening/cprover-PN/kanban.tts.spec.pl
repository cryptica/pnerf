place('s0').
place('s1').
place('s2').
place('s3').
place('s4').
place('s5').
place('s6').
place('s7').
place('s8').
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
place('l10').
place('l11').
place('l12').
place('l13').
place('l14').
place('l15').
place('l16').
transition(t1, ['l0', 's0'], ['s0', 'l3']).
transition(t2, ['l0', 's0'], ['s0', 'l7']).
transition(t3, ['l0', 's0'], ['s0', 'l11']).
transition(t4, ['l0', 's0'], ['s0', 'l15']).
transition(t5, ['l0', 's0'], ['s1', 'l3']).
transition(t6, ['l0', 's1'], ['s2', 'l7']).
transition(t7, ['l0', 's2'], ['s3', 'l11']).
transition(t8, ['l0', 's3'], ['s4', 'l15']).
transition(t9, ['l1', 's4'], ['s4', 'l2']).
transition(t10, ['l1', 's4'], ['s4', 'l4']).
transition(t11, ['l2', 's4'], ['s4', 'l1']).
transition(t12, ['l3', 's4'], ['s4', 'l1']).
transition(t13, ['l4', 's4'], ['s5', 'l3']).
transition(t14, ['l5', 's4'], ['s4', 'l6']).
transition(t15, ['l5', 's4'], ['s4', 'l8']).
transition(t16, ['l6', 's4'], ['s4', 'l5']).
transition(t17, ['l8', 's4'], ['s7', 'l7']).
transition(t18, ['l9', 's4'], ['s4', 'l10']).
transition(t19, ['l9', 's4'], ['s4', 'l12']).
transition(t20, ['l10', 's4'], ['s4', 'l9']).
transition(t21, ['l13', 's4'], ['s4', 'l14']).
transition(t22, ['l13', 's4'], ['s4', 'l16']).
transition(t23, ['l14', 's4'], ['s4', 'l13']).
transition(t24, ['l16', 's4'], ['s4', 'l15']).
transition(t25, ['l7', 's5'], ['s6', 'l5']).
transition(t26, ['l11', 's6'], ['s4', 'l9']).
transition(t27, ['l12', 's7'], ['s8', 'l11']).
transition(t28, ['l15', 's8'], ['s4', 'l13']).
init('l0', init1).
cond('(>= init1 1)').
init('s0', 1).
cond('(>= s4 1)').
target('s4', 1).
cond('(>= l5 2)').
target('l5', 2).
cond('(>= l7 4)').
target('l7', 4).
cond('(>= l11 4)').
target('l11', 4).
cond('(>= l14 6)').
target('l14', 6).
cond('(>= l15 4)').
target('l15', 4).
