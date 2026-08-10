Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test119.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_29_03_39_24_709_8527638verit.v". Abort.
  Verit_Checker "x2020_07_29_03_39_24_709_8527638.smt_in" "x2020_07_29_03_39_24_709_8527638.smt_inproofnew".
End test119.

