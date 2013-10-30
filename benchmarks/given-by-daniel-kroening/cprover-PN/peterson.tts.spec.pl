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
place('s18').
place('s19').
place('s20').
place('s21').
place('s22').
place('s23').
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
transition(t1, ['l0', 's0'], ['s1', 'l1']).
transition(t2, ['l0', 's1'], ['s2', 'l5']).
transition(t3, ['l0', 's2'], ['s3', 'l8']).
transition(t4, ['l0', 's3'], ['s4', 'l10']).
transition(t5, ['l0', 's4'], ['s5', 'l11']).
transition(t6, ['l1', 's5'], ['s6', 'l2']).
transition(t7, ['l2', 's5'], ['s7', 'l3']).
transition(t8, ['l2', 's5'], ['s8', 'l3']).
transition(t9, ['l3', 's5'], ['s10', 'l4']).
transition(t10, ['l3', 's5'], ['s12', 'l4']).
transition(t11, ['l4', 's5'], ['s14', 'l1']).
transition(t12, ['l5', 's5'], ['s19', 'l14']).
transition(t13, ['l7', 's5'], ['s17', 'l13']).
transition(t14, ['l8', 's5'], ['s16', 'l7']).
transition(t15, ['l8', 's5'], ['s21', 'l14']).
transition(t16, ['l9', 's5'], ['s23', 'l10']).
transition(t17, ['l10', 's5'], ['s15', 'l9']).
transition(t18, ['l5', 's6'], ['s5', 'l6']).
transition(t19, ['l7', 's7'], ['s5', 'l8']).
transition(t20, ['l8', 's8'], ['s9', 'l0']).
transition(t21, ['l0', 's9'], ['s5', 'l8']).
transition(t22, ['l10', 's10'], ['s11', 'l0']).
transition(t23, ['l0', 's11'], ['s5', 'l10']).
transition(t24, ['l7', 's12'], ['s13', 'l0']).
transition(t25, ['l0', 's13'], ['s5', 'l7']).
transition(t26, ['l6', 's14'], ['s5', 'l5']).
transition(t27, ['l11', 's15'], ['s5', 'l12']).
transition(t28, ['l12', 's16'], ['s5', 'l13']).
transition(t29, ['l12', 's17'], ['s18', 'l0']).
transition(t30, ['l0', 's18'], ['s5', 'l7']).
transition(t31, ['l13', 's19'], ['s20', 'l0']).
transition(t32, ['l0', 's20'], ['s5', 'l5']).
transition(t33, ['l13', 's21'], ['s22', 'l0']).
transition(t34, ['l0', 's22'], ['s5', 'l8']).
transition(t35, ['l14', 's23'], ['s5', 'l11']).
init('l0', 1).
transition(init1, [], ['l0']).
init('s0', 1).
cond('(>= s5 1)').
target('s5', 1).
cond('(>= l4 1)').
target('l4', 1).
cond('(>= l14 1)').
target('l14', 1).
