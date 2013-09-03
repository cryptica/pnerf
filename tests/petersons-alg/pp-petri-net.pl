place(p1, [u6], [u1]).
place(p2, [u1], [u3,u2]).
place(p3, [u3,u2], [u5,u4]).
place(p4, [u5,u4], [u6]).
place(q1, [v6], [v1]).
place(q2, [v1], [v3,v2]).
place(q3, [v3,v2], [v5,v4]).
place(q4, [v5,v4], [v6]).
place(hold1, [v5,u3,u2], [v5,v3,u3]).
place(hold2, [v3,v2,u5], [v2,u5,u2]).
place(m1t, [u1], [u6]).
place(m1f, [v4,u6], [v4,u1]).
place(m2t, [v1], [v6]).
place(m2f, [v6,u4], [v1,u4]).

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

init(p1, 1).
init(q1, 1).
init(m1f, 1).
init(hold1, 1).
init(m2f, 1).

cond('(> p4 0)').
cond('(> q4 0)').
