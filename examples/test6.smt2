(set-logic UFLIA)
(declare-fun op_0 () Bool)
(assert (not (or op_0 (not op_0))))
(check-sat)
(exit)
