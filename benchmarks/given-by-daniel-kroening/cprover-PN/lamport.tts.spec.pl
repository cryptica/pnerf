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
place('s13').
place('s14').
place('s15').
place('s16').
place('s17').
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
transition(t1, ['l0', 's0'], ['s1', 'l2']).
transition(t2, ['l0', 's1'], ['s2', 'l5']).
transition(t3, ['l0', 's2'], ['s3', 'l6']).
transition(t4, ['l0', 's3'], ['s4', 'l11']).
transition(t5, ['l1', 's4'], ['s5', 'l2']).
transition(t6, ['l2', 's4'], ['s6', 'l3']).
transition(t7, ['l3', 's4'], ['s7', 'l1']).
transition(t8, ['l4', 's4'], ['s9', 'l7']).
transition(t9, ['l5', 's4'], ['s12', 'l11']).
transition(t10, ['l5', 's4'], ['s14', 'l10']).
transition(t11, ['l6', 's4'], ['s17', 'l9']).
transition(t12, ['l7', 's4'], ['s11', 'l6']).
transition(t13, ['l10', 's4'], ['s16', 'l6']).
transition(t14, ['l4', 's5'], ['s4', 'l5']).
transition(t15, ['l5', 's6'], ['s4', 'l4']).
transition(t16, ['l6', 's7'], ['s8', 'l0']).
transition(t17, ['l0', 's8'], ['s4', 'l6']).
transition(t18, ['l9', 's9'], ['s10', 'l0']).
transition(t19, ['l0', 's10'], ['s4', 'l4']).
transition(t20, ['l0', 's11'], ['s4', 'l8']).
transition(t21, ['l8', 's12'], ['s13', 'l0']).
transition(t22, ['l0', 's13'], ['s4', 'l5']).
transition(t23, ['l9', 's14'], ['s15', 'l0']).
transition(t24, ['l0', 's15'], ['s4', 'l5']).
transition(t25, ['l0', 's16'], ['s4', 'l11']).
transition(t26, ['l11', 's17'], ['s4', 'l0']).
init('l0', init1).
cond('(>= init1 1)').
init('s0', 1).
cond('(>= s4 1)').
target('s4', 1).
cond('(>= l1 1)').
target('l1', 1).
cond('(>= l10 1)').
target('l10', 1).
