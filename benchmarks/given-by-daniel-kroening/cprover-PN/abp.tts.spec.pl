place(s0).
place(s1).
place(s2).
place(s3).
place(s4).
place(s5).
place(s6).
place(s7).
place(s8).
place(s9).
place(s10).
place(s11).
place(s12).
place(s13).
place(s14).
place(s15).
place(s16).
place(s17).
place(s18).
place(s19).
place(s20).
place(s21).
place(s22).
place(s23).
place(s24).
place(s25).
place(s26).
place(s27).
place(s28).
place(l0).
place(l1).
place(l2).
place(l3).
place(l4).
place(l5).
place(l6).
place(l7).
place(l8).
place(l9).
place(l10).
place(l11).
place(l12).
transition(t1, [l0, s0], [s1, l1]).
transition(t2, [l0, s1], [s2, l5]).
transition(t3, [l0, s2], [s3, l8]).
transition(t4, [l0, s3], [s4, l9]).
transition(t5, [l1, s4], [s5, l2]).
transition(t6, [l1, s4], [s8, l5]).
transition(t7, [l1, s4], [s11, l6]).
transition(t8, [l2, s4], [s6, l5]).
transition(t9, [l2, s4], [s10, l1]).
transition(t10, [l2, s4], [s13, l7]).
transition(t11, [l3, s4], [s24, l5]).
transition(t12, [l4, s4], [s23, l5]).
transition(t13, [l5, s4], [s17, l4]).
transition(t14, [l5, s4], [s20, l3]).
transition(t15, [l5, s4], [s25, l4]).
transition(t16, [l5, s4], [s27, l3]).
transition(t17, [l6, s4], [s16, l8]).
transition(t18, [l7, s4], [s15, l8]).
transition(t19, [l3, s5], [s4, l5]).
transition(t20, [l3, s6], [s7, l0]).
transition(t21, [l0, s7], [s4, l2]).
transition(t22, [l4, s8], [s9, l0]).
transition(t23, [l0, s9], [s4, l1]).
transition(t24, [l4, s10], [s4, l5]).
transition(t25, [l8, s11], [s12, l0]).
transition(t26, [l0, s12], [s4, l1]).
transition(t27, [l8, s13], [s14, l0]).
transition(t28, [l0, s14], [s4, l2]).
transition(t29, [l0, s15], [s4, l11]).
transition(t30, [l0, s16], [s4, l11]).
transition(t31, [l7, s17], [s18, l8]).
transition(t32, [l9, s18], [s19, l0]).
transition(t33, [l0, s19], [s4, l9]).
transition(t34, [l6, s20], [s21, l8]).
transition(t35, [l10, s21], [s22, l0]).
transition(t36, [l0, s22], [s4, l10]).
transition(t37, [l0, s23], [s4, l12]).
transition(t38, [l0, s24], [s4, l12]).
transition(t39, [l7, s25], [s26, l8]).
transition(t40, [l10, s26], [s4, l9]).
transition(t41, [l6, s27], [s28, l8]).
transition(t42, [l9, s28], [s4, l10]).
init(l0, init1).
cond('(>= init1 1)').
init(s0, 1).
cond('(>= s4 1)').
target(s4, 1).
cond('(>= l3 2)').
target(l3, 2).
cond('(>= l5 1)').
target(l5, 1).
cond('(>= l6 1)').
target(l6, 1).
