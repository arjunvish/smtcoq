; --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --multi-trigger-linear --no-statistics --random-seed=1 --lang=smt2 --continued-execution --tlimit 30000
(set-option :produce-unsat-cores true)
(set-logic AUFLIA)
(declare-fun a_d () Bool)
(declare-fun b_d () Bool)
(assert (! (not (= (not (= a_d b_d)) (or (and a_d (not b_d)) (and b_d (not a_d))))) :named a0))
(check-sat)
;(get-unsat-core)
