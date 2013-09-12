(declare-fun s1 () Bool)
(declare-fun s2 () Bool)
(declare-fun s3 () Bool)
(declare-fun s4 () Bool)
(declare-fun s5 () Bool)
(declare-fun s6 () Bool)

(assert (implies s1 (and s3 (or s1 s2 s6))))
(assert (implies s2 s3))
(assert (implies s3 (and s1 (or s3 s4 s5))))
(assert (implies s4 s1))
(assert (implies s5 (or s1 s2 s6)))
(assert (implies s6 (or s3 s4 s5)))

(assert (or s1 s5))

(assert (not s1))
(assert (not s2))
(assert (not s4))
(assert (not s5))

(check-sat)
(get-model)
