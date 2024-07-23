(set-logic QF_UFLIA)
(set-option :sygus-core-connective false)
(declare-fun succ (Int ) Int)
(declare-fun pow (Int Int ) Int)
(declare-fun j () Int)
(declare-fun zdiv (Int Int ) Int)
(assert (<= 0 j))
(get-abduct A (<= (+ (* (succ j) 0) (succ j)) (pow (+ (zdiv (+ (succ j) 0) 2) 1) 2)))

