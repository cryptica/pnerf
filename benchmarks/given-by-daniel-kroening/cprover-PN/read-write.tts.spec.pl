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
transition(t1, ['l0', 's0'], ['s1', 'l3']).
transition(t2, ['l0', 's1'], ['s2', 'l9']).
transition(t3, ['l0', 's2'], ['s3', 'l12']).
transition(t4, ['l0', 's3'], ['s4', 'l13']).
transition(t5, ['l1', 's4'], ['s4', 'l2']).
transition(t6, ['l2', 's4'], ['s5', 'l1']).
transition(t7, ['l2', 's4'], ['s7', 'l3']).
transition(t8, ['l3', 's4'], ['s6', 'l2']).
transition(t9, ['l4', 's4'], ['s9', 'l5']).
transition(t10, ['l5', 's4'], ['s15', 'l9']).
transition(t11, ['l7', 's4'], ['s4', 'l8']).
transition(t12, ['l9', 's4'], ['s10', 'l5']).
transition(t13, ['l10', 's4'], ['s21', 'l12']).
transition(t14, ['l5', 's5'], ['s4', 'l4']).
transition(t15, ['l12', 's6'], ['s4', 'l0']).
transition(t16, ['l0', 's7'], ['s8', 'l6']).
transition(t17, ['l0', 's8'], ['s4', 'l10']).
transition(t18, ['l8', 's9'], ['s4', 'l7']).
transition(t19, ['l13', 's10'], ['s11', 'l5']).
transition(t20, ['l0', 's11'], ['s12', 'l5']).
transition(t21, ['l0', 's12'], ['s13', 'l5']).
transition(t22, ['l0', 's13'], ['s14', 'l5']).
transition(t23, ['l0', 's14'], ['s4', 'l8']).
transition(t24, ['l5', 's15'], ['s16', 'l11']).
transition(t25, ['l5', 's16'], ['s17', 'l0']).
transition(t26, ['l5', 's17'], ['s18', 'l0']).
transition(t27, ['l5', 's18'], ['s19', 'l0']).
transition(t28, ['l6', 's19'], ['s20', 'l0']).
transition(t29, ['l8', 's20'], ['s4', 'l0']).
transition(t30, ['l11', 's21'], ['s4', 'l13']).
init('l0', 1).
transition(init1, [], ['l0']).
init('s0', 1).
target(1, [(['s4'],1),(['l4'],1),(['l11'],1)]).
