Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test113.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_29_03_48_18_914_8656120verit.v". Abort.
  Verit_Checker "x2020_07_29_03_48_18_914_8656120.smt_in" "x2020_07_29_03_48_18_914_8656120.smt_inproofnew".
End test113.

