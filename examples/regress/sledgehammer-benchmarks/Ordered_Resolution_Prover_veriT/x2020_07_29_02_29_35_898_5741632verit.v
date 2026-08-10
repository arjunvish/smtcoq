Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test97.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_29_02_29_35_898_5741632verit.v". Abort.
  Verit_Checker "x2020_07_29_02_29_35_898_5741632.smt_in" "x2020_07_29_02_29_35_898_5741632.smt_inproofnew".
End test97.

