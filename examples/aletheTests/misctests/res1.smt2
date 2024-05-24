;Testing: Can have two pivots
;Seems like yes we can
(set-logic UFLIA)
(declare-fun x () Bool)
(declare-fun y () Bool)
(assert (or x y))
(assert (or (not x) (not y)))
(assert (not (or y (not y))))
(check-sat)
(exit)