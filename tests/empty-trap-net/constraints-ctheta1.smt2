(declare-fun s1 () Bool)
(declare-fun s2 () Bool)
(declare-fun s3 () Bool)
(declare-fun s4 () Bool)

(assert (implies s1 s2))
(assert (implies s2 (or s3 s4)))
(assert (implies s3 (or s2 s3)))

(assert (not s3))
(assert (not s4))

(assert false)

(check-sat)
(get-model)
