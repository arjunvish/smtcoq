Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test130.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_29_01_46_40_335_5636392verit.v". Abort.
  Verit_Checker "x2020_07_29_01_46_40_335_5636392.smt_in" "x2020_07_29_01_46_40_335_5636392.smt_inproofnew".
End test130.

