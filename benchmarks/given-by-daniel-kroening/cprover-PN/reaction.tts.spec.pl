place(s0).
place(s1).
place(s2).
place(s3).
place(s4).
place(s5).
place(s6).
place(s7).
place(s8).
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
transition(t1, [l0, s0], [s1, l1]).
transition(t2, [l0, s1], [s2, l2]).
transition(t3, [l0, s2], [s3, l7]).
transition(t4, [l0, s3], [s4, l8]).
transition(t5, [l1, s4], [s4, l6]).
transition(t6, [l2, s4], [s4, l5]).
transition(t7, [l7, s4], [s4, l0]).
transition(t8, [l8, s4], [s5, l4]).
transition(t9, [l8, s4], [s6, l3]).
transition(t10, [l8, s4], [s8, l3]).
transition(t11, [l0, s5], [s4, l9]).
transition(t12, [l0, s6], [s7, l5]).
transition(t13, [l0, s7], [s4, l7]).
transition(t14, [l0, s8], [s4, l9]).
init(l0, init1).
cond('(>= init1 1)').
init(s0, 1).
cond('(>= s4 1)').
target(s4, 1).
cond('(>= l9 2)').
target(l9, 2).
