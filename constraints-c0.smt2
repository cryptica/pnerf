(declare-const p1 Int)
(declare-const p2 Int)
(declare-const p3 Int)
(declare-const p4 Int)
(declare-const q1 Int)
(declare-const q2 Int)
(declare-const q3 Int)
(declare-const q4 Int)
(declare-const m1f Int)
(declare-const m1t Int)
(declare-const m2t Int)
(declare-const m2f Int)
(declare-const hold1 Int)
(declare-const hold2 Int)
(declare-const u1 Int)
(declare-const u2 Int)
(declare-const u3 Int)
(declare-const u4 Int)
(declare-const u5 Int)
(declare-const u6 Int)
(declare-const v1 Int)
(declare-const v2 Int)
(declare-const v3 Int)
(declare-const v4 Int)
(declare-const v5 Int)
(declare-const v6 Int)
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
(assert (= p1 (+ 1 u6 (- u1))))
(assert (= p2 (+ 0 u1 (- u2) (- u3))))
(assert (= p3 (+ 0 u2 u3 (- u4) (- u5))))
(assert (= p4 (+ 0 u4 u5 (- u6))))
(assert (= q1 (+ 1 v6 (- v1))))
(assert (= q2 (+ 0 v1 (- v2) (- v3))))
(assert (= q3 (+ 0 v2 v3 (- v4) (- v5))))
(assert (= q4 (+ 0 v4 v5 (- v6))))
(assert (= m1f (+ 1 u6 (- u1))))
(assert (= m1t (+ 0 u1 (- u6))))
(assert (= m2f (+ 1 v6 (- v1))))
(assert (= m2t (+ 0 v1 (- v6))))
(assert (= hold1 (+ 1 u2 (- v3))))
(assert (= hold2 (+ 0 v3 (- u2))))
(assert (> p4 0))
(assert (> q4 0))
(check-sat)
(get-model)
