; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --multi-trigger-linear --no-statistics --random-seed=1 --lang=smt2 --continued-execution --tlimit 30000
(set-option :produce-unsat-cores true)
(set-logic AUFLIA)
(declare-fun x () Bool)
(assert (! x :named a0))
(assert (! (not x) :named a1))
(assert (! (= x x) :named a2))
(check-sat)
;(get-unsat-core)