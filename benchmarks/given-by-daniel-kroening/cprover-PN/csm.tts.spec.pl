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
place(l13).
place(l14).
transition(t1, [l0, s0], [s0, l8]).
transition(t2, [l0, s0], [s1, l6]).
transition(t3, [l0, s1], [s2, l7]).
transition(t4, [l0, s2], [s3, l8]).
transition(t5, [l0, s3], [s4, l14]).
transition(t6, [l1, s4], [s4, l2]).
transition(t7, [l2, s4], [s7, l6]).
transition(t8, [l2, s4], [s8, l6]).
transition(t9, [l5, s4], [s5, l1]).
transition(t10, [l5, s4], [s6, l1]).
transition(t11, [l6, s4], [s4, l5]).
transition(t12, [l7, s4], [s9, l10]).
transition(t13, [l8, s4], [s4, l9]).
transition(t14, [l10, s4], [s10, l7]).
transition(t15, [l11, s4], [s4, l8]).
transition(t16, [l11, s4], [s4, l13]).
transition(t17, [l12, s4], [s11, l9]).
transition(t18, [l13, s4], [s12, l12]).
transition(t19, [l10, s5], [s4, l3]).
transition(t20, [l7, s6], [s4, l4]).
transition(t21, [l4, s7], [s4, l7]).
transition(t22, [l3, s8], [s4, l10]).
transition(t23, [l9, s9], [s4, l0]).
transition(t24, [l0, s10], [s4, l11]).
transition(t25, [l0, s11], [s4, l14]).
transition(t26, [l14, s12], [s4, l0]).
init(l0, init1).
cond('(>= init1 1)').
init(s0).
cond('(>= s4 1)').
target(s4, 1).
cond('(>= l10 2)').
target(l10, 2).
