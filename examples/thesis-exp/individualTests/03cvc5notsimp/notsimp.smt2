(set-logic AUFLIA)
(declare-fun x () Bool)
(assert (not (= (not (not x)) x)))
(check-sat)
