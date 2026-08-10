Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test118.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_29_04_26_46_622_8897120.v". Abort.
  Verit_Checker "x2020_07_29_04_26_46_622_8897120.smt_in" "x2020_07_29_04_26_46_622_8897120.smt_inproofnew".
End test118.
