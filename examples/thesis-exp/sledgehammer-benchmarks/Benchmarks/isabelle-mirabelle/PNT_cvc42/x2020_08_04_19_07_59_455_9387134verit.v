Add Rec LoadPath "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test94.
  Goal True. idtac "". idtac "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks/Benchmarks/isabelle-mirabelle/PNT_cvc42/x2020_08_04_19_07_59_455_9387134verit.v". Abort.
  Verit_Checker "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks/Benchmarks/isabelle-mirabelle/PNT_cvc42/x2020_08_04_19_07_59_455_9387134.smt_in" "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks/Benchmarks/isabelle-mirabelle/PNT_cvc42/x2020_08_04_19_07_59_455_9387134.smt_inproofnew".
End test94.

