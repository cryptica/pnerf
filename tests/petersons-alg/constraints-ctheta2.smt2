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

; constraints on theta being a trap

(assert (implies p1 (or p2 m1t)))
(assert (implies p2 (and (or p3 hold1) (or p3 hold1))))
(assert (implies p3 (and (or p4 m2f) (or p4 hold2))))
(assert (implies p4 (or p1 m1f)))

(assert (implies q1 (or q2 m2t)))
(assert (implies q2 (and (or q3 hold2) (or q3 hold2))))
(assert (implies q3 (and (or q4 m1f) (or q4 hold1))))
(assert (implies q4 (or q1 m2f)))

(assert (implies m1f (and (or p2 m1t) (or q4 m1f))))
(assert (implies m1t (or p1 m1f)))

(assert (implies m2f (and (or q2 m1t) (or p4 m2f))))
(assert (implies m2t (or q1 m2f)))

(assert (implies hold1 (and (or q3 hold2) (or q4 hold1) (or p3 hold1))))
(assert (implies hold2 (and (or p3 hold1) (or p4 hold2) (or q3 hold2))))

; constraints on theta being marked initially

(assert (or p1 q1 m1f m2f hold1))

; constraints on theta not being marked in the assignment

(assert (and (not p4) (not q4) (not m1t) (not m2t) (not hold2)))

; check if sat

(check-sat)

; get model

(get-model)

