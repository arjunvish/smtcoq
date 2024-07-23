(set-option :print-success true)
(set-option :produce-assignments true)
(set-option :produce-abducts true)
(set-option :incremental true)
(set-option :sygus-core-connective false)
(set-logic QF_UFLIA)
(declare-fun p () Int)
(declare-fun n () Int)
(declare-fun m () Int)
(declare-fun mul (Int Int ) Int)
(assert (= n (mul m p)))
;(get-abduct A (= n (- (mul m (- p))))
;  ((GB Bool) 
;   ;(GI Int)
;  )
;  (
;    ((GB Bool (= (- (mul m (-p))) (mul m p))
;     ;(true false (= GI GI) (<= GI GI) (not GB) (and GB GB))
;    ))
;    ;(GI Int (n m p 1 0 (+ GI GI) (- GI GI) (mul GI GI)))
;  )
;)
(get-abduct A (= n (- (mul m (- p)))))
;(define-fun __internal_abduct () Bool (and (= n p) (= n 0)))
;(define-fun __internal_abduct () Bool (and (= n p) (= 0 (mul m n))))
;(define-fun __internal_abduct () Bool (and (= n 0) (= p (mul m p))))
;(define-fun __internal_abduct () Bool (and (= p 0) (= p (mul m p))))
;(define-fun __internal_abduct () Bool (= n (- 0 (mul m (- 0 p)))))

