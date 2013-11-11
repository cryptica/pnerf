place(s1, [t1], [t2,t1]).
place(s2, [t1], [t2]).
place(s3, [t3,t2], [t3]).
place(s4, [t3], []).
place(s5, [t3], [t1]).
place(s6, [t1], [t3]).

transition(t1, [s1,s5], [s1,s2,s6]).
transition(t2, [s1,s2], [s3]).
transition(t3, [s3,s6], [s3,s4,s5]).

weight(s1, t1, 1).
weight(s1, t2, 1).
weight(s2, t2, 1).
weight(s3, t3, 1).
weight(s5, t1, 1).
weight(s6, t3, 1).
weight(t1, s1, 1).
weight(t1, s2, 1).
weight(t1, s6, 1).
weight(t2, s3, 1).
weight(t3, s3, 1).
weight(t3, s4, 1).
weight(t3, s5, 1).

init(s1, 1).
init(s5, 1).

cond('(>= s1 1)').
cond('(>= s2 1)').
cond('(>= s4 1)').
cond('(>= s5 1)').

target([([s1],1),([s2],1),([s4],1),([s5],1)]).
