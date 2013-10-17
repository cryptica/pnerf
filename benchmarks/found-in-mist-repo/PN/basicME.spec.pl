place(x0).
place(x1).
place(x2).
place(x3).
place(x4).
transition(t1, [x0, x1, x2], [x1, x3]).
transition(t2, [x0, x1, x2], [x2, x4]).
transition(t3, [x3], [x0, x2]).
transition(t4, [x4], [x0, x1]).
init(x0, init1).
cond('(>= init1 1)').
init(x1, 1).
init(x2, 1).
cond('(>= x3 1)').
target(x3, 1).
cond('(>= x4 1)').
target(x4, 1).
cond('(>= x3 2)').
target(x3, 2).
cond('(>= x4 2)').
target(x4, 2).
