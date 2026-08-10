Add Rec LoadPath "../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test12.
  Goal True. idtac "". idtac "isabelle-mirabelle/BO_cvc42/x2020_08_03_15_23_28_446_6397402cvc5.v". Abort.
  Verit_Checker "x2020_08_03_15_23_28_446_6397402.smt_in" "x2020_08_03_15_23_28_446_6397402.cvc5oldpf".
End test12.

