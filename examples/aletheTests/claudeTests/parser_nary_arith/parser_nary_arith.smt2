(set-logic QF_LIA)
(declare-fun x () Int)
(assert (not (= x x)))
(check-sat)
