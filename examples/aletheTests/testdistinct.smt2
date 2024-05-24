(set-logic QF_UFLIA)
(assert (not (= (distinct 1) true)))
(check-sat)
(exit)