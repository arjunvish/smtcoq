No exceptions are raised, but checker fails.

Proof File: x2020_07_24_02_50_45_899_5005750.smt_inproofnew
SMT File: x2020_07_24_02_50_45_899_5005750.smt_in
Path: /home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks/Benchmarks/isabelle-mirabelle/HOL-Library/smt_verit/

Problem:
This step:
```
(step t3 (cl (= (= (ite p_d true q_d) (or p_d q_d)) (= (or p_d q_d) (or p_d q_d)))) :rule cong :premises (t2))
```
creates an unsound resolution due to the `process_cong` tranformation in veritAst. For congruence over 
equality, the transformation is equipped to handle equalities where 2 of the 4 terms are syntactically 
equal (for instance in `(x = y) = (a = b)`) but here 3 of the 4 terms are syntactically equal, so our transformation fails. It produces a resolution where there is an extra term, so the Coq checker fails.

Fix: Extend `process_cong` with a case for when 3 of the 4 literals of the equality are equal (in the worst case, you would have an explicit case for each of the cases)