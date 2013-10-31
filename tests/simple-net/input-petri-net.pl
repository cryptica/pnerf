place(s1).
place(s2).
place(s3).

transition(t1, [s1], [s2,s3]).
transition(t2, [s2,s3], [s1]).

init(s1).

cond('(>= s1 1)').
cond('(>= s2 1)').

target(s1, 1).
target(s2, 1).
