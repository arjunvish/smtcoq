Add Rec LoadPath "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test2.
  Goal True. idtac "". idtac "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-norulesnoexists/Benchmarks/isabelle-mirabelle/BO_cvc42/x2020_08_03_15_05_23_096_5606264.smt_in". Abort.
  Verit_Checker "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-norulesnoexists/Benchmarks/isabelle-mirabelle/BO_cvc42/x2020_08_03_15_05_23_096_5606264.smt_in" "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-norulesnoexists/Benchmarks/isabelle-mirabelle/BO_cvc42/x2020_08_03_15_05_23_096_5606264.smt_inproofnew".
End test2.
