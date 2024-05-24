(set-logic UFLIA)
(declare-fun x () Bool)
(declare-fun m () Int)
(declare-fun y () Bool)
(declare-fun n () Int)
(assert (not (=
                (not (=> (ite  x 
                	       (ite  y (= (+ (* 2 m) 1) (+ (* 2 n) 1)) (= (+ (* 2 m) 1) (* 2 n)))
                	       (ite  y (= (* 2 m) (+ (* 2 n) 1)) (= (* 2 m) (* 2 n))))
                	  (and  (=>  x y) (=>  y x) (= m n))))
                (and  	 (ite  x 
                	       (ite  y (= (+ (* 2 m) 1) (+ (* 2 n) 1)) (= (+ (* 2 m) 1) (* 2 n))) 
                	       (ite  y (= (* 2 m) (+ (* 2 n) 1)) (= (* 2 m) (* 2 n))))
                      	 (not (and  (=>  x y) (=>  y x) (= m n))))
)))
(check-sat)
(exit)