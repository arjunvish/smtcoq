Add Rec LoadPath "../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test2.
  Goal True. idtac "". idtac "isabelle-mirabelle/BO_cvc42/x2020_08_03_15_05_23_096_5606264cvc5.v". Abort.
  Verit_Checker "x2020_08_03_15_05_23_096_5606264.smt_in" "x2020_08_03_15_05_23_096_5606264.cvc5oldpf".
End test2.

