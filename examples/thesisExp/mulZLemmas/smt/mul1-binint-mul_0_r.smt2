;this is an interesting example that demonstrates shortcomings of 
;the abduction solver
;since the abducts are quantifier-free, the best it can do is
;mul (x + y) 0 = 0 ^ mul x 0 = 0 ^ mul y 0 = 0
;as opposed to
;forall x. mul x 0 = 0
(set-option :print-success true)
(set-option :produce-assignments true)
(set-option :produce-abducts true)
(set-option :incremental true)
(set-option :sygus-core-connective false)
(set-logic QF_UFLIA)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun mul (Int Int ) Int)
(get-abduct A (= (mul (+ x y) 0) (+ (mul x 0) (mul y 0))))
;(define-fun A () Bool (and (= (mul y y) y) (= 0 y)))
;takes 1 min
