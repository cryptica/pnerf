(declare-fun s1 () Bool)
(declare-fun s2 () Bool)
(declare-fun s3 () Bool)
(declare-fun s4 () Bool)

(declare-fun o_t1 () Bool)
(declare-fun o_t2 () Bool)
(declare-fun o_t3 () Bool)

(assert (implies s1 o_t1))
(assert (implies s2 o_t3))
(assert (implies s3 o_t2))
(assert (implies s4 true))

(assert (implies o_t1 s2))
(assert (implies o_t2 (or s2 s3)))
(assert (implies o_t3 (or s3 s4)))

(assert false)

(assert (not s3))
(assert (not s4))

(check-sat)
(get-model)
