(set-option :produce-assignments true)
(set-option :produce-proofs true)
(set-logic QF_UFLIA)
;(declare-fun x () Int)
;(declare-fun y () Int)
(assert (not (= 0 0)))
(check-sat)
