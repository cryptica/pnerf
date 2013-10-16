place(start).
place(x).
place(_x).
place(ping).
place(pong).
place(main).
transition(t1, [start], [x, main]).
transition(t2, [start], [_ _x, main]).
transition(t3, [main, _x], [_x, ping]).
transition(t4, [main, x], [x, _ _ping]).
transition(t5, [ping, _x], [_x, _ _pong]).
transition(t6, [pong, x], [x, _ _ping]).
init(start).
cond('(>= pong 1)').
target(pong, 1).
 _cond('(>= x 1)').
target(x, 1).
