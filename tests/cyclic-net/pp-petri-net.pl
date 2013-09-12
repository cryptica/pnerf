place(s1, [t4,t1], [t2,t1]).
place(s2, [t1], [t2]).
place(s3, [t3,t2], [t4,t3]).
place(s4, [t3], [t4]).
place(s5, [t3], [t1]).
place(s6, [t1], [t3]).

transition(t1, [s1,s5], [s1,s2,s6]).
transition(t2, [s1,s2], [s3]).
transition(t3, [s3,s6], [s3,s4,s5]).
transition(t4, [s3,s4], [s1]).

init(s1, 1).
init(s5, 1).
cond('(> s1 0)').
cond('(> s2 0)').
cond('(> s4 0)').
cond('(> s5 0)').

