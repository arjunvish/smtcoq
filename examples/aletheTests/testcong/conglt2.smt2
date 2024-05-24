(set-logic UFLIA)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun P (Int Int) Bool)
(assert (= a x))
(assert (= b y))
(assert (P a b))
(assert (not (P x y)))
(check-sat)
(exit)
