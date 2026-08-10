Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test102.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_28_21_05_57_088_7410378.v". Abort.
  Verit_Checker "x2020_07_28_21_05_57_088_7410378.smt_in" "x2020_07_28_21_05_57_088_7410378.smt_inproofnew".
End test102.
