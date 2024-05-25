# First Problem
Initial exception was raised for subproof with multiple assumptions:
```
Message: | VeritAst.preprocess_certif: failed to preprocess || process_subproof: expecting the last step of the certificate to be a discharge step at id t7 |
Position: Line 46 Position 1
```

Proof File: x2020_08_03_16_40_35_239_4899098.cvc5pf
SMT File: x2020_08_03_16_40_35_239_4899098.smt_in
Path: /home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks/Benchmarks/isabelle-mirabelle/BO_cvc42/

Additionally, the same problem arose for:
Proof File: x2020_07_24_02_50_00_147_4983028.cvc5pf
SMT File: x2020_07_24_02_50_00_147_4983028.smt_in
Path: /home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks/Benchmarks/isabelle-mirabelle/HOL-Library/smt_verit/

Proof File: x2020_07_31_07_55_13_484_7016530.cvc5pf
SMT File: x2020_07_31_07_55_13_484_7016530.smt_in
Path: /home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks/Benchmarks/isabelle-mirabelle/Green_cvc42/

Proof File: x2020_07_29_00_24_03_784_9778214.cvc5pf
SMT File: x2020_07_29_00_24_03_784_9778214.smt_in
Path: /home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks/Benchmarks/Ordered_Resolution_Prover_veriT/

Proof File: x2020_07_29_03_48_18_914_8656120.cvc5pf
SMT File: x2020_07_29_03_48_18_914_8656120.smt_in
Path: /home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks/Benchmarks/Ordered_Resolution_Prover_veriT/

Problem:
Subproof has two assumptions:
```
(anchor :step t7)
(assume t7.a0 (not (= (wt_d ground_heads_var_d delta_d arity_sym_d wt_sym_d ua_d) (wt_d ground_heads_var_d delta_d arity_sym_d wt_sym_d sa_d))))
(assume t7.a1 (= (wt_d ground_heads_var_d delta_d arity_sym_d wt_sym_d sa_d) (wt_d ground_heads_var_d delta_d arity_sym_d wt_sym_d ta_d)))
```
So when the discharge step is encountered:
```
(step t7 (cl (not (not (= (wt_d ground_heads_var_d delta_d arity_sym_d wt_sym_d ua_d) (wt_d ground_heads_var_d delta_d arity_sym_d wt_sym_d sa_d)))) (not (= (wt_d ground_heads_var_d delta_d arity_sym_d wt_sym_d sa_d) (wt_d ground_heads_var_d delta_d arity_sym_d wt_sym_d ta_d))) (not (= (wt_d ground_heads_var_d delta_d arity_sym_d wt_sym_d ua_d) (wt_d ground_heads_var_d delta_d arity_sym_d wt_sym_d ta_d)))) :rule subproof :discharge (t7.a0 t7.a1))
```
Our transformation expects a clause of the form `~a, c` but instead it sees `~a1, ~a2, c`. 

Fix: Extend `process_subproof` for multiple hypotheses.

# Second Problem
When we fixed some of the issues arising from `02cvc5AndProj`, the problem has changed to the following:
```
Message: | VeritAst.preprocess_certif: failed to preprocess || process_cong: can't fetch premises to congr (no implicit equalities case) at id t7.t3 |
Position: Line 46 Position 1
```
Problem: a congruence inside a subproof is accessing premises from before the subproof. 

Fix: In a recursive call to process_cong for subproofs, give it the entire proof, not just the subproof. Fixed!