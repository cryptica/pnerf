(declare-fun s1 () Bool)
(declare-fun s2 () Bool)
(declare-fun s3 () Bool)
(declare-fun s4 () Bool)
(declare-fun s5 () Bool)
(declare-fun t1 () Int)
(declare-fun t2 () Int)
(declare-fun t3 () Int)
(declare-fun o_t1 () Bool)
(declare-fun o_t2 () Bool)
(declare-fun o_t3 () Bool)

(assert (implies s1 o_t1))
(assert (implies s2 o_t1))
(assert (implies s3 o_t3))
(assert (implies s4 o_t2))
(assert (implies s5 true))

(assert (= o_t1 (implies (> t1 0) (or s1 s2 s3))))
(assert (= o_t2 (implies (> t2 0) (or s3 s4))))
(assert (= o_t3 (implies (> t3 0) (or s4 s5))))

(assert (not s1))
(assert (not s4))
(assert (not s5))

(assert (or s3 s4 s5))

(assert (= t1 0))
(assert (= t2 1))
(assert (= t3 1))

(check-sat)
(get-model)
