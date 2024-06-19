No exceptions are raised, but checker fails.

Proof File: x2020_07_29_02_01_16_644_5442968.smt_inproofnew
SMT File: x2020_07_29_02_01_16_644_5442968.smt_in
Path: /home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks/Benchmarks/Ordered_Resolution_Prover_veriT/

Problem:
The transitivity step in `t5`:
```
(step t3 (cl (= (=> (not (true_clss_d (i_of_d n_d) n_d)) false) (not (not (true_clss_d (i_of_d n_d) n_d))))) :rule implies_simplify)
(step t4 (cl (= (not (not (true_clss_d (i_of_d n_d) n_d))) (true_clss_d (i_of_d n_d) n_d))) :rule not_simplify)
(step t5 (cl (= (=> (not (true_clss_d (i_of_d n_d) n_d)) false) (true_clss_d (i_of_d n_d) n_d))) :rule trans :premises (t3 t4))
```
uses `t4` as a premise, and SMTCoq sees `t4` as an equality since it eliminates double negations. In the transformation, 
however, we aren't eliminating implicit equalities, so it creates an unsound and unnecessary resolution.

Fix: Extend `process_trans` so that when one of the premises to the transitivity (in the `iff` case) is an equality (modulo  
double negation elimination), we can remove it from consideration. FIXED!