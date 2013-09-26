place(s1, [t1], [t1]).
place(s2, [t1], [t1]).
place(s3, [t2,t1], [t3]).
place(s4, [t3,t2], [t2]).
place(s5, [t3], []).

transition(t1, [s1,s2], [s1,s2,s3]).
transition(t2, [s4], [s3,s4]).
transition(t3, [s3], [s4,s5]).

weight(s1, t1, 1).
weight(s2, t1, 1).
weight(t1, s1, 1).
weight(t1, s2, 1).
weight(t1, s3, 1).
weight(s4, t2, 1).
weight(t2, s3, 1).
weight(t2, s4, 1).
weight(s3, t3, 1).
weight(t3, s4, 1).
weight(t3, s5, 1).

init(s1, 1).

cond('(>= s5 1)').

target(s5, 1).
