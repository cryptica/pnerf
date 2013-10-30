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
place('l17').
place('l18').
transition(t1, ['l0', 's0'], ['s0', 'l1']).
transition(t2, ['l0', 's0'], ['s0', 'l2']).
transition(t3, ['l0', 's0'], ['s0', 'l17']).
transition(t4, ['l0', 's0'], ['s0', 'l18']).
transition(t5, ['l0', 's0'], ['s1', 'l1']).
transition(t6, ['l0', 's1'], ['s2', 'l2']).
transition(t7, ['l0', 's2'], ['s3', 'l8']).
transition(t8, ['l0', 's3'], ['s4', 'l8']).
transition(t9, ['l0', 's4'], ['s5', 'l8']).
transition(t10, ['l0', 's5'], ['s6', 'l17']).
transition(t11, ['l0', 's6'], ['s7', 'l18']).
transition(t12, ['l1', 's7'], ['s7', 'l3']).
transition(t13, ['l2', 's7'], ['s7', 'l6']).
transition(t14, ['l3', 's7'], ['s8', 'l4']).
transition(t15, ['l4', 's7'], ['s9', 'l1']).
transition(t16, ['l5', 's7'], ['s10', 'l2']).
transition(t17, ['l6', 's7'], ['s11', 'l5']).
transition(t18, ['l7', 's7'], ['s7', 'l8']).
transition(t19, ['l8', 's7'], ['s7', 'l10']).
transition(t20, ['l9', 's7'], ['s7', 'l8']).
transition(t21, ['l10', 's7'], ['s7', 'l7']).
transition(t22, ['l10', 's7'], ['s7', 'l9']).
transition(t23, ['l10', 's7'], ['s7', 'l11']).
transition(t24, ['l10', 's7'], ['s7', 'l12']).
transition(t25, ['l11', 's7'], ['s7', 'l8']).
transition(t26, ['l11', 's7'], ['s12', 'l14']).
transition(t27, ['l12', 's7'], ['s7', 'l8']).
transition(t28, ['l12', 's7'], ['s15', 'l15']).
transition(t29, ['l14', 's7'], ['s13', 'l8']).
transition(t30, ['l15', 's7'], ['s14', 'l8']).
transition(t31, ['l17', 's7'], ['s7', 'l13']).
transition(t32, ['l18', 's7'], ['s7', 'l16']).
transition(t33, ['l7', 's8'], ['s7', 'l0']).
transition(t34, ['l0', 's9'], ['s7', 'l8']).
transition(t35, ['l0', 's10'], ['s7', 'l8']).
transition(t36, ['l9', 's11'], ['s7', 'l0']).
transition(t37, ['l13', 's12'], ['s7', 'l0']).
transition(t38, ['l0', 's13'], ['s7', 'l17']).
transition(t39, ['l0', 's14'], ['s7', 'l18']).
transition(t40, ['l16', 's15'], ['s7', 'l0']).
init('l0', 1).
transition(init1, [], ['l0']).
init('s0', 1).
cond('(>= s7 1)').
target('s7', 1).
cond('(>= l4 1)').
target('l4', 1).
cond('(>= l5 1)').
target('l5', 1).
cond('(>= l14 1)').
target('l14', 1).
cond('(>= l15 1)').
target('l15', 1).
