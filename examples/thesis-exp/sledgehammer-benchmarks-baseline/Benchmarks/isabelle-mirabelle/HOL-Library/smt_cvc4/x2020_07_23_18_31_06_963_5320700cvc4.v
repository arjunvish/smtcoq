Add Rec LoadPath "/home/arjun/Desktop/smtcoq/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test78.
  Goal True. idtac "". idtac "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-baseline/Benchmarks/isabelle-mirabelle/HOL-Library/smt_cvc4/x2020_07_23_18_31_06_963_5320700cvc4.v". Abort.
  Lfsc_Checker "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-baseline/Benchmarks/isabelle-mirabelle/HOL-Library/smt_cvc4/x2020_07_23_18_31_06_963_5320700.smt_in" "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-baseline/Benchmarks/isabelle-mirabelle/HOL-Library/smt_cvc4/x2020_07_23_18_31_06_963_5320700.cvc4pf".
End test78.

