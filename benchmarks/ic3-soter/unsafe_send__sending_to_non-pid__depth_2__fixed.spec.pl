place('s0').
place('s1').
place('s2').
place('s3').
place('s4').
place('s5').
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
transition(t1, ['l0', 's0'], ['s1', 'l1']).
transition(t2, ['l0', 's1'], ['l0', 's2']).
transition(t3, ['l1', 's1'], ['s1', 'l8']).
transition(t4, ['l2', 's1'], ['s1', 'l3']).
transition(t5, ['l3', 's1'], ['s1', 'l9']).
transition(t6, ['l4', 's1'], ['s1', 'l5']).
transition(t7, ['l5', 's1'], ['s3', 'l15']).
transition(t8, ['l6', 's1'], ['s1', 'l7']).
transition(t9, ['l7', 's1'], ['s1', 'l18']).
transition(t10, ['l8', 's1'], ['s1', 'l6']).
transition(t11, ['l9', 's1'], ['s4', 'l11']).
transition(t12, ['l12', 's1'], ['s1', 'l2']).
transition(t13, ['l13', 's1'], ['s1', 'l4']).
transition(t14, ['l14', 's1'], ['s1', 'l12']).
transition(t15, ['l15', 's1'], ['s1', 'l21']).
transition(t16, ['l16', 's1'], ['s1', 'l17']).
transition(t17, ['l17', 's1'], ['s1', 'l13']).
transition(t18, ['l18', 's1'], ['s1', 'l16']).
transition(t19, ['l19', 's1'], ['s1', 'l20']).
transition(t20, ['l20', 's1'], ['s1', 'l23']).
transition(t21, ['l21', 's1'], ['s1', 'l22']).
transition(t22, ['l22', 's1'], ['s1', 'l25']).
transition(t23, ['l24', 's1'], ['s1', 'l19']).
transition(t24, ['l25', 's1'], ['s5', 'l0']).
transition(t25, ['l26', 's1'], ['s1', 'l24']).
transition(t26, ['l23', 's2'], ['s2', 'l28']).
transition(t27, ['l0', 's3'], ['s1', 'l14']).
transition(t28, ['l0', 's4'], ['s1', 'l10']).
transition(t29, ['l11', 's5'], ['s1', 'l26']).
init('l0', 1).
transition(init1, [], ['l0']).
init('s0', 1).
target(1, [(['s2'],1),(['l28'],1)]).
