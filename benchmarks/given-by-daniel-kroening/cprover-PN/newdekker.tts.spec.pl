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
place('s24').
place('s25').
place('s26').
place('s27').
place('s28').
place('s29').
place('s30').
place('s31').
place('s32').
place('s33').
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
transition(t1, ['l0', 's0'], ['s1', 'l1']).
transition(t2, ['l0', 's1'], ['s2', 'l6']).
transition(t3, ['l0', 's2'], ['s3', 'l11']).
transition(t4, ['l0', 's3'], ['s4', 'l13']).
transition(t5, ['l0', 's4'], ['s5', 'l15']).
transition(t6, ['l1', 's5'], ['s6', 'l2']).
transition(t7, ['l2', 's5'], ['s8', 'l3']).
transition(t8, ['l2', 's5'], ['s26', 'l5']).
transition(t9, ['l3', 's5'], ['s12', 'l2']).
transition(t10, ['l3', 's5'], ['s16', 'l4']).
transition(t11, ['l4', 's5'], ['s22', 'l1']).
transition(t12, ['l5', 's5'], ['s30', 'l1']).
transition(t13, ['l6', 's5'], ['s7', 'l7']).
transition(t14, ['l7', 's5'], ['s10', 'l8']).
transition(t15, ['l7', 's5'], ['s28', 'l10']).
transition(t16, ['l8', 's5'], ['s14', 'l7']).
transition(t17, ['l8', 's5'], ['s19', 'l9']).
transition(t18, ['l9', 's5'], ['s24', 'l6']).
transition(t19, ['l10', 's5'], ['s32', 'l6']).
transition(t20, ['l11', 's6'], ['s5', 'l12']).
transition(t21, ['l13', 's7'], ['s5', 'l14']).
transition(t22, ['l14', 's8'], ['s9', 'l0']).
transition(t23, ['l0', 's9'], ['s5', 'l14']).
transition(t24, ['l12', 's10'], ['s11', 'l0']).
transition(t25, ['l0', 's11'], ['s5', 'l12']).
transition(t26, ['l15', 's12'], ['s13', 'l0']).
transition(t27, ['l0', 's13'], ['s5', 'l15']).
transition(t28, ['l16', 's14'], ['s15', 'l0']).
transition(t29, ['l0', 's15'], ['s5', 'l16']).
transition(t30, ['l12', 's16'], ['s17', 'l11']).
transition(t31, ['l16', 's17'], ['s18', 'l0']).
transition(t32, ['l0', 's18'], ['s5', 'l16']).
transition(t33, ['l14', 's19'], ['s20', 'l13']).
transition(t34, ['l15', 's20'], ['s21', 'l0']).
transition(t35, ['l0', 's21'], ['s5', 'l15']).
transition(t36, ['l15', 's22'], ['s23', 'l0']).
transition(t37, ['l0', 's23'], ['s5', 'l15']).
transition(t38, ['l16', 's24'], ['s25', 'l0']).
transition(t39, ['l0', 's25'], ['s5', 'l16']).
transition(t40, ['l13', 's26'], ['s27', 'l0']).
transition(t41, ['l0', 's27'], ['s5', 'l13']).
transition(t42, ['l11', 's28'], ['s29', 'l0']).
transition(t43, ['l0', 's29'], ['s5', 'l11']).
transition(t44, ['l12', 's30'], ['s31', 'l11']).
transition(t45, ['l15', 's31'], ['s5', 'l16']).
transition(t46, ['l14', 's32'], ['s33', 'l13']).
transition(t47, ['l16', 's33'], ['s5', 'l15']).
init('l0', 1).
transition(init1, [], ['l0']).
init('s0', 1).
target([(['s5'],1),(['l5'],1),(['l10'],1)]).
