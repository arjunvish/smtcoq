Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test131.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_28_23_18_50_649_7061430.v". Abort.
  Verit_Checker "x2020_07_28_23_18_50_649_7061430.smt_in" "x2020_07_28_23_18_50_649_7061430.smt_inproofnew".
End test131.
