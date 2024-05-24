Add Rec LoadPath "/home/arjun/Desktop/smtcoq/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test42.
  Goal True. idtac "". idtac "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-baseline/Benchmarks/isabelle-mirabelle/HOL-Library/smt_verit/x2020_07_24_02_50_45_899_5005750verit2016.v". Abort.
  Verit_Checker "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-baseline/Benchmarks/isabelle-mirabelle/HOL-Library/smt_verit/x2020_07_24_02_50_45_899_5005750.smt_in" "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-baseline/Benchmarks/isabelle-mirabelle/HOL-Library/smt_verit/x2020_07_24_02_50_45_899_5005750.verit2016pf".
End test42.

