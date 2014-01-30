place(cs1).
place(idle1).
place(nid1).
place(req1).
place(id1).

place(cs2).
place(idle2).
place(req2).
place(after_you2).
place(await2).
place(id2).

transition(u1, [cs1, nid1], [idle1, id1]).
transition(u2, [idle1, id1], [req1, nid1]).
transition(u3, [req1, id2], [cs1, id2]).

transition(v1, [req2, nid1], [after_you2, nid1]).
transition(v2, [after_you2], [id2, await2]).
transition(v3, [id1, await2], [id1, idle2]).
transition(v4, [req2, id1], [cs2, id1]).
transition(v5, [cs2], [idle2, id2]).
transition(v6, [idle2, id2], [req2]).

init(id1).
init(id2).
init(idle1).
init(idle2).

target(1, [([cs1,cs2],2)]).
