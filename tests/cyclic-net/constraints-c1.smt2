(declare-fun s1 () Int)
(declare-fun s2 () Int)
(declare-fun s3 () Int)
(declare-fun s4 () Int)
(declare-fun s5 () Int)
(declare-fun s6 () Int)
(declare-fun t1 () Int)
(declare-fun t2 () Int)
(declare-fun t3 () Int)
(declare-fun t4 () Int)
(assert (>= s1 0))
(assert (>= s2 0))
(assert (>= s3 0))
(assert (>= s4 0))
(assert (>= s5 0))
(assert (>= s6 0))
(assert (>= t1 0))
(assert (>= t2 0))
(assert (>= t3 0))
(assert (>= t4 0))
(assert (= s1 (+ 1 t4 (- t2))))
(assert (= s2 (+ 0 t1 (- t2))))
(assert (= s3 (+ 0 t2 (- t4))))
(assert (= s4 (+ 0 t3 (- t4))))
(assert (= s5 (+ 1 t3 (- t1))))
(assert (= s6 (+ 0 t1 (- t3))))
(assert (> s1 0))
(assert (> s5 0))
(assert (> s4 0))
(assert (implies (and (> t1 0) (= t2 0) (> t3 0) (= t4 0)) (>= s3 1)))
(check-sat)
(get-model)
