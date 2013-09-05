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
place(l5).
place(l6).
transition(t1, [l0, s0], [s1, l1]).
transition(t2, [l0, s1], [s2, l5]).
transition(t3, [l0, s2], [s3, l5]).
transition(t4, [l1, s3], [s3, l2]).
transition(t5, [l2, s3], [s4, l6]).
transition(t6, [l4, s3], [s5, l1]).
transition(t7, [l5, s3], [s3, l3]).
transition(t8, [l6, s3], [s3, l4]).
transition(t9, [l3, s4], [s3, l0]).
transition(t10, [l0, s5], [s3, l5]).
init(l0, init1).
cond('(>= init1 1)').
init(s0).
cond('(>= s3 1)').
cond('(>= l6 2)').
