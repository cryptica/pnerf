place(s1).
place(s2).
place(s3).
place(s4).
place(s5).

transition(t1, [s1], [s2]).
transition(t2, [s1], [s3]).
transition(t3, [s2, s3], [s4, s5]).
transition(t4, [s4], [s5]).

init(s1, 1).

target(1, [([s5],1)]).
