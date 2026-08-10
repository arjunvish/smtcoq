Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test133.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_28_23_18_50_649_7061430verit.v". Abort.
  Verit_Checker "x2020_07_28_23_18_50_649_7061430.smt_in" "x2020_07_28_23_18_50_649_7061430.smt_inproofnew".
End test133.

