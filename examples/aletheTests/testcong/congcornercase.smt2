(set-logic UFLIA)
(assert (= (not true) false))
(assert (not (= (and true (not true)) (and true false))))
(check-sat)
(exit)
