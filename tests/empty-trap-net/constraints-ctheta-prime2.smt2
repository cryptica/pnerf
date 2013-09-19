(declare-fun s1 () Bool)
(declare-fun s2 () Bool)
(declare-fun s3 () Bool)
(declare-fun s4 () Bool)
(declare-fun s5 () Bool)
(declare-fun i_t1 () Bool)
(declare-fun i_t2 () Bool)
(declare-fun i_t3 () Bool)
(declare-fun o_t1 () Bool)
(declare-fun o_t2 () Bool)
(declare-fun o_t3 () Bool)

(assert (implies s1 o_t1))
(assert (implies s2 o_t1))
(assert (implies s3 o_t3))
(assert (implies s4 o_t2))
(assert (implies s5 true))

(assert (implies s1 i_t1))
(assert (implies s2 i_t1))
(assert (implies s3 (and i_t2 i_t1)))
(assert (implies s4 (and i_t3 i_t2)))
(assert (implies s5 i_t3))

(assert (implies o_t1 i_t1))
(assert (implies o_t2 i_t2))
(assert (implies o_t3 i_t3))

(assert (implies i_t1 (or s1 s2 s3)))
(assert (implies i_t2 (or s3 s4)))
(assert (implies i_t3 (or s4 s5)))

(assert (implies o_t1 (or s1 s2)))
(assert (implies o_t2 s4))
(assert (implies o_t3 s3))

(assert (or o_t1 o_t2 o_t3))

(assert (or o_t1 (not i_t1)))
(assert (or o_t2 (not i_t2)))
(assert (or o_t3 (not i_t3)))

(assert (not s1))

(check-sat)
(get-model)
