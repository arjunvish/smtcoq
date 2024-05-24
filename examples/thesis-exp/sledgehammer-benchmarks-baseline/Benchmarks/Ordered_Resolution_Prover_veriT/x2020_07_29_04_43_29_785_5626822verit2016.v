Add Rec LoadPath "/home/arjun/Desktop/smtcoq/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test133.
  Goal True. idtac "". idtac "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-baseline/Benchmarks/Ordered_Resolution_Prover_veriT/x2020_07_29_04_43_29_785_5626822verit2016.v". Abort.
  Verit_Checker "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-baseline/Benchmarks/Ordered_Resolution_Prover_veriT/x2020_07_29_04_43_29_785_5626822.smt_in" "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-baseline/Benchmarks/Ordered_Resolution_Prover_veriT/x2020_07_29_04_43_29_785_5626822.verit2016pf".
End test133.

