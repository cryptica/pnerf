place(p1).
place(p2).
place(p3).
place(b1).
place(nb1).

place(q1).
place(q2).
place(q3).
place(q4).
place(q5).
place(nb2).

transition(s1, [p1,nb1], [p2,b1]).
transition(s2, [p2,nb2], [p3,nb2]).
transition(s3, [p3,b1], [p1,nb1]).

transition(t1, [q1, nb2], [q2]).
transition(t2, [q2, b1], [q3, b1]).
transition(t3, [q3], [q4, nb2]).
transition(t4, [q4, nb1], [q1, nb1]).
transition(t5, [q2, nb1], [q5, nb1]).
transition(t6, [q5], [q1, nb2]).

init(p1).
init(q1).
init(nb1).
init(nb2).

target(1, [([p3], 1), ([q5], 1)]).
