place(p1).
place(p2).
place(p3).
place(p4).
place(q1).
place(q2).
place(q3).
place(q4).
place(m1f).
place(m1t).
place(m2f).
place(m2t).
place(hold1).
place(hold2).

transition(u1, [p1,m1f], [p2,m1t]).
transition(u2, [p2,hold2], [p3,hold1]).
transition(u3, [p2,hold1], [p3,hold1]).
transition(u4, [p3,m2f], [p4,m2f]).
transition(u5, [p3,hold2], [p4,hold2]).
transition(u6, [p4,m1t], [p1,m1f]).
transition(v1, [q1,m2f], [q2,m2t]).
transition(v2, [q2,hold2], [q3,hold2]).
transition(v3, [q2,hold1], [q3,hold2]).
transition(v4, [q3,m1f], [q4,m1f]).
transition(v5, [q3,hold1], [q4,hold1]).
transition(v6, [q4,m2t], [q1,m2f]).

init(p1).
init(q1).
init(m1f).
init(hold1).
init(m2f).

cond('(> p4 0)').
cond('(> q4 0)').
