place(x0).
place(x1).
place(x2).
place(x3).
place(x4).
place(x5).
place(x6).
place(x7).
place(x8).
place(x9).
place(x10).
place(x11).
place(x12).
transition(t1, [(x0, 2)], [(x4, 2), x7]).
transition(t2, [x1], [x4, x8]).
transition(t3, [x2], [x5, x9]).
transition(t4, [(x4, 4), x5], [x6, x10]).
transition(t5, [x3], [x6, x11]).
transition(t6, [(x6, 2)], [(x0, 3), x1, x2, x3, x12]).
cond('(>= x7 3)').
target(x7, 3).
cond('(>= x8 2)').
target(x8, 2).
cond('(>= x9 2)').
target(x9, 2).
cond('(>= x10 2)').
target(x10, 2).
cond('(>= x11 2)').
target(x11, 2).
cond('(>= x12 2)').
target(x12, 2).
