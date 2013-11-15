(declare-fun nc () Int)
(declare-fun cs1 () Int)
(declare-fun cs2 () Int)
(declare-fun s1 () Int)
(declare-fun s2 () Int)
(declare-fun target_1 () Int)
(declare-fun trap_1 () Int)
(assert (>= 0 (+ 0 cs1 (- nc) (- s1))))
(assert (>= 0 (+ 0 cs2 (- nc) (- s2))))
(assert (>= 0 (+ 0 (- cs1) nc s1)))
(assert (>= 0 (+ 0 (- cs2) nc s2)))
(assert (< (+ 0 (* 2 nc) s1 s2) (+ (* 2 target_1) trap_1)))
(assert (>= nc 0))
(assert (>= cs1 target_1))
(assert (>= cs2 target_1))
(assert (>= s1 trap_1))
(assert (>= s2 trap_1))
(assert (>= target_1 0))
(assert (>= trap_1 0))
(check-sat)
(get-model)
