place(s0).
place(s1).
place(s2).
place(s3).
place(s4).
place(s5).
place(l0).
place(l1).
place(l2).
place(l3).
place(l4).
transition(t1, [l0, s0], [s1, l2]).
transition(t2, [l0, s1], [s2, l2]).
transition(t3, [l0, s2], [s3, l4]).
transition(t4, [l0, s3], [s4, l4]).
transition(t5, [l1, s4], [s4, l3]).
transition(t6, [l2, s4], [s5, l1]).
transition(t7, [l4, s5], [s4, l0]).
init(l0, init1).
cond('(>= init1 1)').
init(s0).
cond('(>= s4 1)').
target(s4, 1).
cond('(>= l1 2)').
target(l1, 2).
