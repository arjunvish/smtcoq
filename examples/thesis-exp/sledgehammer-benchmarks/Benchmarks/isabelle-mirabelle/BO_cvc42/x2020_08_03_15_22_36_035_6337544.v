Add Rec LoadPath "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test13.
  Goal True. idtac "". idtac "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-norulesnoexists/Benchmarks/isabelle-mirabelle/BO_cvc42/x2020_08_03_15_22_36_035_6337544.smt_in". Abort.
  Verit_Checker "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-norulesnoexists/Benchmarks/isabelle-mirabelle/BO_cvc42/x2020_08_03_15_22_36_035_6337544.smt_in" "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-norulesnoexists/Benchmarks/isabelle-mirabelle/BO_cvc42/x2020_08_03_15_22_36_035_6337544.smt_inproofnew".
End test13.
