(declare-fun t_1 () Int)
(declare-fun s1 () Int)
(declare-fun s2 () Int)
(declare-fun s3 () Int)
(declare-fun s4 () Int)
(declare-fun s5 () Int)
(assert (>= 0 (+ 0 (- s1) s2)))
(assert (>= 0 (+ 0 (- s1) s3)))
(assert (>= 0 (+ 0 (- s2) (- s3) s4 (+ s5 t_1))))
(assert (>= 0 (+ 0 (- s4) (+ s5 t_1))))
(assert (< (+ 0 s1) t_1))
(assert (>= t_1 0))
(assert (>= s1 0))
(assert (>= s2 0))
(assert (>= s3 0))
(assert (>= s4 0))
(assert (>= s5 0))
(check-sat)
(get-model)
