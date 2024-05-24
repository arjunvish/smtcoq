Add Rec LoadPath "/home/arjun/Desktop/smtcoq/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test91.
  Goal True. idtac "". idtac "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-baseline/Benchmarks/isabelle-mirabelle/PNT_cvc42/x2020_08_04_17_34_35_557_9411026verit2016.v". Abort.
  Verit_Checker "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-baseline/Benchmarks/isabelle-mirabelle/PNT_cvc42/x2020_08_04_17_34_35_557_9411026.smt_in" "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-baseline/Benchmarks/isabelle-mirabelle/PNT_cvc42/x2020_08_04_17_34_35_557_9411026.verit2016pf".
End test91.

