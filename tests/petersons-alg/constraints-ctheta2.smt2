; variables for places being part of the trap

(declare-const p1 Bool)
(declare-const p2 Bool)
(declare-const p3 Bool)
(declare-const p4 Bool)

(declare-const q1 Bool)
(declare-const q2 Bool)
(declare-const q3 Bool)
(declare-const q4 Bool)

(declare-const m1f Bool)
(declare-const m1t Bool)
(declare-const m2t Bool)
(declare-const m2f Bool)
(declare-const hold1 Bool)
(declare-const hold2 Bool)

(declare-fun o_u1 () Bool)
(declare-fun o_u2 () Bool)
(declare-fun o_u3 () Bool)
(declare-fun o_u4 () Bool)
(declare-fun o_u5 () Bool)
(declare-fun o_u6 () Bool)
(declare-fun o_v1 () Bool)
(declare-fun o_v2 () Bool)
(declare-fun o_v3 () Bool)
(declare-fun o_v4 () Bool)
(declare-fun o_v5 () Bool)
(declare-fun o_v6 () Bool)

; constraints on theta being a trap

(assert (implies p1 o_u1))
(assert (implies p2 (and o_u3 o_u2)))
(assert (implies p3 (and o_u5 o_u4)))
(assert (implies p4 o_u6))
(assert (implies q1 o_v1))
(assert (implies q2 (and o_v3 o_v2)))
(assert (implies q3 (and o_v5 o_v4)))
(assert (implies q4 o_v6))
(assert (implies m1f (and o_v4 o_u1)))
(assert (implies m1t o_u6))
(assert (implies m2f (and o_v1 o_u4)))
(assert (implies m2t o_v6))
(assert (implies hold1 (and o_v5 o_v3 o_u3)))
(assert (implies hold2 (and o_v2 o_u5 o_u2)))

(assert (implies o_u1 (or p2 m1t)))
(assert (implies o_u2 (or p3 hold1)))
(assert (implies o_u3 (or p3 hold1)))
(assert (implies o_u4 (or p4 m2f)))
(assert (implies o_u5 (or p4 hold2)))
(assert (implies o_u6 (or p1 m1f)))
(assert (implies o_v1 (or q2 m2t)))
(assert (implies o_v2 (or q3 hold2)))
(assert (implies o_v3 (or q3 hold2)))
(assert (implies o_v4 (or q4 m1f)))
(assert (implies o_v5 (or q4 hold1)))
(assert (implies o_v6 (or q1 m2f)))


; constraints on theta being marked initially

(assert (or p1 q1 m1f m2f hold1))

; constraints on theta not being marked in the assignment

(assert (and (not p4) (not q4) (not m1t) (not m2t) (not hold2)))

; check if sat

(check-sat)

; get model

(get-model)

