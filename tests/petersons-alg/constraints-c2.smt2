(declare-fun p1 () Int)
(declare-fun p2 () Int)
(declare-fun p3 () Int)
(declare-fun p4 () Int)
(declare-fun q1 () Int)
(declare-fun q2 () Int)
(declare-fun q3 () Int)
(declare-fun q4 () Int)
(declare-fun m1f () Int)
(declare-fun m1t () Int)
(declare-fun m2t () Int)
(declare-fun m2f () Int)
(declare-fun hold1 () Int)
(declare-fun hold2 () Int)
(declare-fun u1 () Int)
(declare-fun u2 () Int)
(declare-fun u3 () Int)
(declare-fun u4 () Int)
(declare-fun u5 () Int)
(declare-fun u6 () Int)
(declare-fun v1 () Int)
(declare-fun v2 () Int)
(declare-fun v3 () Int)
(declare-fun v4 () Int)
(declare-fun v5 () Int)
(declare-fun v6 () Int)
(assert (>= p1 0))
(assert (>= p2 0))
(assert (>= p3 0))
(assert (>= p4 0))
(assert (>= q1 0))
(assert (>= q2 0))
(assert (>= q3 0))
(assert (>= q4 0))
(assert (>= m1f 0))
(assert (>= m1t 0))
(assert (>= m2f 0))
(assert (>= m2t 0))
(assert (>= hold1 0))
(assert (>= hold2 0))
(assert (>= u1 0))
(assert (>= u2 0))
(assert (>= u3 0))
(assert (>= u4 0))
(assert (>= u5 0))
(assert (>= u6 0))
(assert (>= v1 0))
(assert (>= v2 0))
(assert (>= v3 0))
(assert (>= v4 0))
(assert (>= v5 0))
(assert (>= v6 0))
(assert (= p1 (+ 1 (- u1) u6)))
(assert (= p2 (+ 0 u1 (- u2) (- u3))))
(assert (= p3 (+ 0 u2 u3 (- u4) (- u5))))
(assert (= p4 (+ 0 u4 u5 (- u6))))
(assert (= q1 (+ 1 (- v1) v6)))
(assert (= q2 (+ 0 v1 (- v2) (- v3))))
(assert (= q3 (+ 0 v2 v3 (- v4) (- v5))))
(assert (= q4 (+ 0 v4 v5 (- v6))))
(assert (= m1f (+ 1 (- u1) u6)))
(assert (= m1t (+ 0 u1 (- u6))))
(assert (= m2f (+ 1 (- v1) v6)))
(assert (= m2t (+ 0 v1 (- v6))))
(assert (= hold1 (+ 1 u2 (- v3))))
(assert (= hold2 (+ 0 (- u2) v3)))
(assert (or (>= (+ p4 q4) 2)))
(assert (>= (+ p3 q2 hold2 m2f) 1))
(assert (>= (+ p2 q3 hold1 m1f) 1))
(check-sat)
(get-model)
