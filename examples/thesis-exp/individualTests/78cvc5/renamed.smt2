; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --multi-trigger-linear --no-statistics --random-seed=1 --lang=smt2 --continued-execution --tlimit 30000
(set-option :produce-unsat-cores true)
(set-logic AUFLIA)
(declare-fun a () Bool)
(declare-fun b () Bool)
(assert (! (not (= (not (= a b)) (or (and a (not b)) (and b (not a))))) :named a0))
(check-sat)
;(get-unsat-core)
