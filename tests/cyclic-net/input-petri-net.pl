place(s1).
place(s2).
place(s3).
place(s4).
place(s5).
place(s6).

transition(t1, [s1,s5], [s1,s2,s6]).
transition(t2, [s1,s2], [s3]).
transition(t3, [s3,s6], [s3,s4,s5]).

init(s1).
init(s5).

cond('(>= s1 1)').
cond('(>= s2 1)').
cond('(>= s4 1)').
cond('(>= s5 1)').

target(s1, 1).
target(s2, 1).
target(s4, 1).
target(s5, 1).
