Add Rec LoadPath "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test5.
  Goal True. idtac "". idtac "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-norulesnoexists/Benchmarks/isabelle-mirabelle/BO_cvc42/x2020_08_03_16_51_50_546_5359382.smt_in". Abort.
  Verit_Checker "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-norulesnoexists/Benchmarks/isabelle-mirabelle/BO_cvc42/x2020_08_03_16_51_50_546_5359382.smt_in" "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-norulesnoexists/Benchmarks/isabelle-mirabelle/BO_cvc42/x2020_08_03_16_51_50_546_5359382.smt_inproofnew".
End test5.
