; --proof-with-sharing --index-fresh-sorts --proof-define-skolems --proof-prune --proof-merge --disable-print-success --disable-banner --max-time=30
(set-option :produce-proofs true)
(set-logic AUFLIA)
(declare-fun x () Bool)
(declare-fun y () Bool)
(assert (! (not (= (ite x true y) (or x y))) :named a0))
(check-sat)
;;;;;;(get-proof)
