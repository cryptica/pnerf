(declare-fun s1 () Real)
(declare-fun s2 () Real)
(declare-fun s3 () Real)
(declare-fun s4 () Real)
(declare-fun s5 () Real)
(declare-fun t1 () Real)
(declare-fun t2 () Real)
(declare-fun t3 () Real)
(declare-fun t4 () Real)
(assert (>= s1 0))
(assert (>= s2 0))
(assert (>= s3 0))
(assert (>= s4 0))
(assert (>= s5 0))
(assert (>= t1 0))
(assert (>= t2 0))
(assert (>= t3 0))
(assert (>= t4 0))
(assert (= s1 (+ 1 (- t1) (- t2))))
(assert (= s2 (+ 0 t1 (- t3))))
(assert (= s3 (+ 0 t2 (- t3))))
(assert (= s4 (+ 0 t3 (- t4))))
(assert (= s5 (+ 0 t3 t4)))
(assert (>= s5 1))
(check-sat)
(get-model)
