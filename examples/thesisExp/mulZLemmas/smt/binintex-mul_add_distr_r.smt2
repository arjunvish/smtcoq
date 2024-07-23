(set-option :print-success true)
(set-option :produce-assignments true)
(set-option :produce-abducts true)
(set-option :incremental true)
(set-logic QF_UFLIA)
(set-option :sygus-core-connective false)
(declare-fun n () Int)
(declare-fun m () Int)
(declare-fun mul (Int Int ) Int)
(assert (= (mul 1 m) m))
(get-abduct A (= (mul (+ n 1) m) (+ (mul n m) m)))
;(define-fun A () Bool (and (= (mul n m) 0) (= 0 n)))

;ideal abduct: mul (+ n 1) m = + (mul n m) (mul 1 m)

;sygus-stream
;(define-fun A () Bool (and (= (mul n m) 0) (= 0 n)))

