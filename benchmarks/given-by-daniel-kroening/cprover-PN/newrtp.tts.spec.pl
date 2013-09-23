place(s0).
place(s1).
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
transition(t2, [l1, s1], [s1, l2]).
transition(t3, [l2, s1], [s1, l3]).
transition(t4, [l3, s1], [s1, l4]).
transition(t5, [l4, s1], [s1, l5]).
transition(t6, [l4, s1], [s1, l9]).
transition(t7, [l5, s1], [s1, l6]).
transition(t8, [l6, s1], [s1, l7]).
transition(t9, [l6, s1], [s1, l8]).
transition(t10, [l6, s1], [s1, l9]).
transition(t11, [l7, s1], [s1, l9]).
transition(t12, [l8, s1], [s1, l9]).
transition(t13, [l9, s1], [s1, l2]).
init(l0, init1).
cond('(>= init1 1)').
init(s0).
cond('(>= s1 1)').
target(s1, 1).
cond('(>= l5 1)').
target(l5, 1).
cond('(>= l9 1)').
target(l9, 1).
