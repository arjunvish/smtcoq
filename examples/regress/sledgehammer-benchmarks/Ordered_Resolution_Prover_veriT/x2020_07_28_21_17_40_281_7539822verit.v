Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test142.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_28_21_17_40_281_7539822verit.v". Abort.
  Verit_Checker "x2020_07_28_21_17_40_281_7539822.smt_in" "x2020_07_28_21_17_40_281_7539822.smt_inproofnew".
End test142.

