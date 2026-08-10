Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test138.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_29_04_20_00_872_8811318verit.v". Abort.
  Verit_Checker "x2020_07_29_04_20_00_872_8811318.smt_in" "x2020_07_29_04_20_00_872_8811318.smt_inproofnew".
End test138.

