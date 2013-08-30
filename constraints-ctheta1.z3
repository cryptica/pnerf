; variables for places being part of the trap

(declare-const bp1 Bool)
(declare-const bp2 Bool)
(declare-const bp3 Bool)
(declare-const bp4 Bool)

(declare-const bq1 Bool)
(declare-const bq2 Bool)
(declare-const bq3 Bool)
(declare-const bq4 Bool)

(declare-const bm1f Bool)
(declare-const bm1t Bool)
(declare-const bm2t Bool)
(declare-const bm2f Bool)
(declare-const bhold1 Bool)
(declare-const bhold2 Bool)

; constraints on theta being a trap

(assert (implies bp1 (or bp2 bm1t)))
(assert (implies bp2 (and (or bp3 bhold1) (or bp3 bhold1))))
(assert (implies bp3 (and (or bp4 bm2f) (or bp4 bhold2))))
(assert (implies bp4 (or bp1 bm1f)))

(assert (implies bq1 (or bq2 bm2t)))
(assert (implies bq2 (and (or bq3 bhold2) (or bq3 bhold2))))
(assert (implies bq3 (and (or bq4 bm1f) (or bq4 bhold1))))
(assert (implies bq4 (or bq1 bm2f)))

(assert (implies bm1f (and (or bp2 bm1t) (or bq4 bm1f))))
(assert (implies bm1t (or bp1 bm1f)))

(assert (implies bm2f (and (or bq2 bm1t) (or bp4 bm2f))))
(assert (implies bm2t (or bq1 bm2f)))

(assert (implies bhold1 (and (or bq3 bhold2) (or bq4 bhold1) (or bp3 bhold1))))
(assert (implies bhold2 (and (or bp3 bhold1) (or bp4 bhold2) (or bq3 bhold2))))

; constraints on theta being marked initially

(assert (or bp1 bq1 bm1f bm2f bhold1))

; constraints on theta not being marked in the assignment

(assert (and (not bp4) (not bq4) (not bm1t) (not bm2t) (not bhold1)))

; check if sat

(check-sat)

; get model

(get-model)

