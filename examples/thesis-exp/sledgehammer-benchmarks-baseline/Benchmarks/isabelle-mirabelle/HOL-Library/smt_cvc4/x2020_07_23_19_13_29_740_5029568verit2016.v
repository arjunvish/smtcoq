Add Rec LoadPath "/home/arjun/Desktop/smtcoq/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test70.
  Goal True. idtac "". idtac "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-baseline/Benchmarks/isabelle-mirabelle/HOL-Library/smt_cvc4/x2020_07_23_19_13_29_740_5029568verit2016.v". Abort.
  Verit_Checker "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-baseline/Benchmarks/isabelle-mirabelle/HOL-Library/smt_cvc4/x2020_07_23_19_13_29_740_5029568.smt_in" "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-baseline/Benchmarks/isabelle-mirabelle/HOL-Library/smt_cvc4/x2020_07_23_19_13_29_740_5029568.verit2016pf".
End test70.

