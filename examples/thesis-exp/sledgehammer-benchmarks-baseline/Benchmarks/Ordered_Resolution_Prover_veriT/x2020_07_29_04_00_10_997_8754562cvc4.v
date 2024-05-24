Add Rec LoadPath "/home/arjun/Desktop/smtcoq/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test123.
  Goal True. idtac "". idtac "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-baseline/Benchmarks/Ordered_Resolution_Prover_veriT/x2020_07_29_04_00_10_997_8754562cvc4.v". Abort.
  Lfsc_Checker "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-baseline/Benchmarks/Ordered_Resolution_Prover_veriT/x2020_07_29_04_00_10_997_8754562.smt_in" "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-baseline/Benchmarks/Ordered_Resolution_Prover_veriT/x2020_07_29_04_00_10_997_8754562.cvc4pf".
End test123.

