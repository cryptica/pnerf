place(s1, [t2], [t1]).
place(s2, [t1], [t2]).
place(s3, [t1], [t2]).

transition(t1, [s1], [s2,s3]).
transition(t2, [s2,s3], [s1]).

weight(s1, t1, 1).
weight(s2, t2, 1).
weight(s3, t2, 1).
weight(t1, s2, 1).
weight(t1, s3, 1).
weight(t2, s1, 1).

init(s1, 1).

cond('(>= s1 1)').
cond('(>= s2 1)').

target(s1, 1).
target(s2, 1).
