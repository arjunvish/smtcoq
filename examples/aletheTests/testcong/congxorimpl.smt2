(set-logic UFLIA)
(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun x () Bool)
(declare-fun y () Bool)
(assert (= b y))
(assert (not (= (xor x b) (xor x y))))
(check-sat)
(exit)
