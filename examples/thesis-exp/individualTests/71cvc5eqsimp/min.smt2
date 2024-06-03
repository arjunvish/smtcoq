(set-option :produce-proofs true)
(set-logic AUFLIA)
(assert (not (= (= true false) false)))
(check-sat)