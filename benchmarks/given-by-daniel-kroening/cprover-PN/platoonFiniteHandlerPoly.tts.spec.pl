place(s0).
place(s1).
place(s2).
place(s3).
place(s4).
place(s5).
place(s6).
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
transition(t1, [l0, s0], [s1, l4]).
transition(t2, [l0, s1], [s2, l10]).
transition(t3, [l1, s2], [s2, l9]).
transition(t4, [l2, s2], [s2, l3]).
transition(t5, [l4, s2], [s2, l6]).
transition(t6, [l5, s2], [s4, l7]).
transition(t7, [l5, s2], [s6, l8]).
transition(t8, [l8, s2], [s3, l1]).
transition(t9, [l9, s2], [s2, l2]).
transition(t10, [l10, s2], [s5, l11]).
transition(t11, [l11, s2], [s2, l5]).
transition(t12, [l0, s3], [s2, l4]).
transition(t13, [l6, s4], [s2, l0]).
transition(t14, [l0, s5], [s2, l10]).
transition(t15, [l7, s6], [s2, l0]).
init(l0, init1).
cond('(>= init1 1)').
init(s0).
cond('(>= s2 1)').
cond('(>= l11 2)').
