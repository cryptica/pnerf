place(p1).
place(p2).
place(p3).
place(bit1).
place(nbit1).

place(q1).
place(q2).
place(q3).
place(q4).
place(q5).
place(nbit2).

transition(s1, [p1,nbit1], [p2,bit1]).
transition(s2, [p2,nbit2], [p3,nbit2]).
transition(s3, [p3,bit1], [p1,nbit1]).

transition(t1, [q1, nbit2], [q2]).
transition(t2, [q2, bit1], [q3, bit1]).
transition(t3, [q3], [q4, nbit2]).
transition(t4, [q4, nbit1], [q1, nbit1]).
transition(t5, [q2, nbit1], [q5, nbit1]).
transition(t6, [q5], [q1, nbit2]).

init(p1).
init(q1).
init(nbit1).
init(nbit2).

target(1, [([p3,q5],2)]).
