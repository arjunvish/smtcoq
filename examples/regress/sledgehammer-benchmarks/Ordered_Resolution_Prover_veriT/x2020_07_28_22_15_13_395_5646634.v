Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test132.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_28_22_15_13_395_5646634.v". Abort.
  Verit_Checker "x2020_07_28_22_15_13_395_5646634.smt_in" "x2020_07_28_22_15_13_395_5646634.smt_inproofnew".
End test132.
