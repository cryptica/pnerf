place(cs1, [t1], [t3]).
place(cs2, [t2], [t4]).
place(nc, [t4,t3], [t2,t1]).
place(s, [t4,t3], [t2,t1]).

transition(t1, [nc,s], [cs1]).
transition(t2, [nc,s], [cs2]).
transition(t3, [cs1], [nc,s]).
transition(t4, [cs2], [nc,s]).

weight(nc, t1, 1).
weight(s, t1, 1).
weight(t1, cs1, 1).
weight(nc, t2, 1).
weight(s, t2, 1).
weight(t2, cs2, 1).
weight(cs1, t3, 1).
weight(t3, nc, 1).
weight(t3, s, 1).
weight(cs2, t4, 1).
weight(t4, nc, 1).
weight(t4, s, 1).

init(nc, 2).
init(s, 1).

target([([cs1,cs2],2)]).

