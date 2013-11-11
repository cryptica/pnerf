(declare-fun cs1 () Bool)
(declare-fun s1 () Bool)
(declare-fun cs2 () Bool)
(declare-fun nc () Bool)
(declare-fun s2 () Bool)

(declare-fun o_t1 () Bool)
(declare-fun o_t2 () Bool)
(declare-fun o_t3 () Bool)
(declare-fun o_t4 () Bool)

(assert (implies cs1 o_t3))
(assert (implies s1 (and o_t2 o_t1)))
(assert (implies cs2 o_t4))
(assert (implies nc (and o_t2 o_t1)))
(assert (implies s2 (and o_t2 o_t1)))

(assert (implies o_t1 (or cs1 s2)))
(assert (implies o_t2 (or cs2 s1)))
(assert (implies o_t3 (or nc s1)))
(assert (implies o_t4 (or nc s2)))

(assert (or nc s1 s2))

(assert (not cs1))
(assert (not cs2))

(check-sat)
(get-model)
