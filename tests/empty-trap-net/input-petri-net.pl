place(s1).
place(s2).
place(s3).
place(s4).

transition(t1, [s1], [s2]).
transition(t2, [s3], [s2,s3]).
transition(t3, [s2], [s3,s4]).

cond('(> s4 0)').
