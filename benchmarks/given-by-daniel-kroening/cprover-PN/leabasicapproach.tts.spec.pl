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
place('s12').
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
transition(t1, ['l0', 's0'], ['s0', 'l5']).
transition(t2, ['l0', 's0'], ['s0', 'l11']).
transition(t3, ['l0', 's0'], ['s1', 'l1']).
transition(t4, ['l0', 's1'], ['s2', 'l3']).
transition(t5, ['l0', 's2'], ['s3', 'l5']).
transition(t6, ['l0', 's3'], ['s4', 'l11']).
transition(t7, ['l1', 's4'], ['s5', 'l2']).
transition(t8, ['l1', 's4'], ['s10', 'l2']).
transition(t9, ['l2', 's4'], ['s8', 'l1']).
transition(t10, ['l2', 's4'], ['s11', 'l1']).
transition(t11, ['l3', 's4'], ['s6', 'l4']).
transition(t12, ['l3', 's4'], ['s9', 'l4']).
transition(t13, ['l4', 's4'], ['s7', 'l3']).
transition(t14, ['l4', 's4'], ['s12', 'l3']).
transition(t15, ['l5', 's4'], ['s4', 'l6']).
transition(t16, ['l10', 's4'], ['s4', 'l5']).
transition(t17, ['l11', 's4'], ['s4', 'l12']).
transition(t18, ['l16', 's4'], ['s4', 'l11']).
transition(t19, ['l6', 's5'], ['s4', 'l7']).
transition(t20, ['l7', 's6'], ['s4', 'l8']).
transition(t21, ['l8', 's7'], ['s4', 'l9']).
transition(t22, ['l9', 's8'], ['s4', 'l10']).
transition(t23, ['l12', 's9'], ['s4', 'l13']).
transition(t24, ['l13', 's10'], ['s4', 'l14']).
transition(t25, ['l14', 's11'], ['s4', 'l15']).
transition(t26, ['l15', 's12'], ['s4', 'l16']).
init('l0', init1).
cond('(>= init1 1)').
init('s0', 1).
cond('(>= s4 1)').
target('s4', 1).
cond('(>= l7 1)').
target('l7', 1).
cond('(>= l13 1)').
target('l13', 1).
