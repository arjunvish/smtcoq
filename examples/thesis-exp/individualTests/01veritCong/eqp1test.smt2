; --proof-with-sharing --index-fresh-sorts --proof-define-skolems --proof-prune --proof-merge --disable-print-success --disable-banner --max-time=30
(set-option :produce-proofs true)
(set-logic AUFLIA)
(declare-fun x () Bool)
(assert x)
(assert (= x x))
(assert (not x))
(check-sat)
