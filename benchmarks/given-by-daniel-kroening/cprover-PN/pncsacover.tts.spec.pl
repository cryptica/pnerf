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
place('l19').
place('l20').
place('l21').
place('l22').
place('l23').
place('l24').
place('l25').
place('l26').
place('l27').
place('l28').
place('l29').
place('l30').
place('l31').
transition(t1, ['l0', 's0'], ['s1', 'l3']).
transition(t2, ['l0', 's1'], ['s2', 'l14']).
transition(t3, ['l1', 's2'], ['s22', 'l13']).
transition(t4, ['l1', 's2'], ['s30', 'l14']).
transition(t5, ['l2', 's2'], ['s29', 'l14']).
transition(t6, ['l3', 's2'], ['s3', 'l4']).
transition(t7, ['l4', 's2'], ['s4', 'l5']).
transition(t8, ['l4', 's2'], ['s14', 'l1']).
transition(t9, ['l5', 's2'], ['s5', 'l6']).
transition(t10, ['l5', 's2'], ['s13', 'l1']).
transition(t11, ['l6', 's2'], ['s6', 'l7']).
transition(t12, ['l7', 's2'], ['s7', 'l8']).
transition(t13, ['l7', 's2'], ['s10', 'l9']).
transition(t14, ['l8', 's2'], ['s2', 'l10']).
transition(t15, ['l8', 's2'], ['s9', 'l7']).
transition(t16, ['l9', 's2'], ['s2', 'l10']).
transition(t17, ['l9', 's2'], ['s12', 'l1']).
transition(t18, ['l10', 's2'], ['s8', 'l2']).
transition(t19, ['l10', 's2'], ['s11', 'l1']).
transition(t20, ['l11', 's2'], ['s2', 'l3']).
transition(t21, ['l11', 's2'], ['s15', 'l3']).
transition(t22, ['l11', 's2'], ['s16', 'l3']).
transition(t23, ['l11', 's2'], ['s17', 'l1']).
transition(t24, ['l14', 's2'], ['s18', 'l15']).
transition(t25, ['l15', 's2'], ['s19', 'l16']).
transition(t26, ['l15', 's2'], ['s28', 'l12']).
transition(t27, ['l16', 's2'], ['s20', 'l17']).
transition(t28, ['l16', 's2'], ['s25', 'l12']).
transition(t29, ['l17', 's2'], ['s2', 'l20']).
transition(t30, ['l17', 's2'], ['s21', 'l18']).
transition(t31, ['l17', 's2'], ['s24', 'l20']).
transition(t32, ['l18', 's2'], ['s2', 'l19']).
transition(t33, ['l18', 's2'], ['s23', 'l17']).
transition(t34, ['l19', 's2'], ['s2', 'l20']).
transition(t35, ['l19', 's2'], ['s27', 'l12']).
transition(t36, ['l20', 's2'], ['s26', 'l12']).
transition(t37, ['l21', 's2'], ['s2', 'l14']).
transition(t38, ['l21', 's2'], ['s31', 'l12']).
transition(t39, ['l0', 's3'], ['s2', 'l22']).
transition(t40, ['l23', 's4'], ['s2', 'l24']).
transition(t41, ['l25', 's5'], ['s2', 'l26']).
transition(t42, ['l28', 's6'], ['s2', 'l0']).
transition(t43, ['l0', 's7'], ['s2', 'l30']).
transition(t44, ['l12', 's8'], ['s2', 'l3']).
transition(t45, ['l31', 's9'], ['s2', 'l0']).
transition(t46, ['l0', 's10'], ['s2', 'l29']).
transition(t47, ['l0', 's11'], ['s2', 'l11']).
transition(t48, ['l27', 's12'], ['s2', 'l11']).
transition(t49, ['l0', 's13'], ['s2', 'l11']).
transition(t50, ['l0', 's14'], ['s2', 'l11']).
transition(t51, ['l13', 's15'], ['s2', 'l0']).
transition(t52, ['l12', 's16'], ['s2', 'l0']).
transition(t53, ['l0', 's17'], ['s2', 'l11']).
transition(t54, ['l22', 's18'], ['s2', 'l23']).
transition(t55, ['l24', 's19'], ['s2', 'l25']).
transition(t56, ['l26', 's20'], ['s2', 'l28']).
transition(t57, ['l30', 's21'], ['s2', 'l0']).
transition(t58, ['l20', 's22'], ['s2', 'l14']).
transition(t59, ['l0', 's23'], ['s2', 'l31']).
transition(t60, ['l29', 's24'], ['s2', 'l27']).
transition(t61, ['l0', 's25'], ['s2', 'l21']).
transition(t62, ['l0', 's26'], ['s2', 'l21']).
transition(t63, ['l0', 's27'], ['s2', 'l21']).
transition(t64, ['l0', 's28'], ['s2', 'l21']).
transition(t65, ['l21', 's29'], ['s2', 'l0']).
transition(t66, ['l21', 's30'], ['s2', 'l0']).
transition(t67, ['l0', 's31'], ['s2', 'l21']).
init('l0', 1).
transition(init1, [], ['l0']).
init('s0', 1).
target([(['s2'],1),(['l13'],1),(['l22'],1),(['l24'],1),(['l29'],1),(['l31'],1)]).
