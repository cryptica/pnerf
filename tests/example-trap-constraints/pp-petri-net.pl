place(cs1, [t1], [t3]).
place(s1, [t3,t2], [t2,t1]).
place(cs2, [t2], [t4]).
place(nc, [t4,t3], [t2,t1]).
place(s2, [t4,t1], [t2,t1]).

transition(t1, [nc,s1,s2], [cs1,s2]).
transition(t2, [nc,s1,s2], [cs2,s1]).
transition(t3, [cs1], [nc,s1]).
transition(t4, [cs2], [nc,s2]).

weight(nc, t1, 1).
weight(s1, t1, 1).
weight(s2, t1, 1).
weight(t1, cs1, 1).
weight(t1, s2, 1).
weight(nc, t2, 1).
weight(s1, t2, 1).
weight(s2, t2, 1).
weight(t2, cs2, 1).
weight(t2, s1, 1).
weight(cs1, t3, 1).
weight(t3, nc, 1).
weight(t3, s1, 1).
weight(cs2, t4, 1).
weight(t4, nc, 1).
weight(t4, s2, 1).

init(nc, 2).
init(s1, 1).
init(s2, 1).

target([([cs1,cs2],2)]).

