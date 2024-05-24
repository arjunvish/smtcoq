Add Rec LoadPath "/home/arjun/Desktop/smtcoq/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test10.
  Goal True. idtac "". idtac "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-baseline/Benchmarks/isabelle-mirabelle/BO_cvc42/x2020_08_03_16_40_35_239_4899098cvc4.v". Abort.
  Lfsc_Checker "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-baseline/Benchmarks/isabelle-mirabelle/BO_cvc42/x2020_08_03_16_40_35_239_4899098.smt_in" "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-baseline/Benchmarks/isabelle-mirabelle/BO_cvc42/x2020_08_03_16_40_35_239_4899098.cvc4pf".
End test10.

