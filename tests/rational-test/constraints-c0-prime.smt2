(declare-fun s1 () Real)
(declare-fun s2 () Real)
(declare-fun s3 () Real)
(declare-fun s4 () Real)
(declare-fun s5 () Real)
(assert (>= 0 (+ (- s1) s2)))
(assert (>= 0 (+ (- s1) s3)))
(assert (>= 0 (+ (- s2) (- s3) s4 s5)))
(assert (>= 0 (+ (- s4) s5)))
(assert (= 1 (+ 0 (- s1) s5)))
(assert (>= s1 0))
(assert (>= s2 0))
(assert (>= s3 0))
(assert (>= s4 0))
(assert (>= s5 0))
(check-sat)
(get-model)
