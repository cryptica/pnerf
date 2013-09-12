place(s1).
place(s2).
place(s3).
place(s4).
place(s5).
place(s6).

transition(t1, [s1,s5], [s1,s2,s6]).
transition(t2, [s1,s2], [s3]).
transition(t3, [s3,s6], [s3,s4,s5]).
transition(t4, [s3,s4], [s1]).

init(s1).
init(s5).

cond('(> s1 0)').
cond('(> s2 0)').
cond('(> s4 0)').
cond('(> s5 0)').
