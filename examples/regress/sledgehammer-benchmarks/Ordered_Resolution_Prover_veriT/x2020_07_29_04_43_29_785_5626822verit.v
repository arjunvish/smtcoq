Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test135.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_29_04_43_29_785_5626822verit.v". Abort.
  Verit_Checker "x2020_07_29_04_43_29_785_5626822.smt_in" "x2020_07_29_04_43_29_785_5626822.smt_inproofnew".
End test135.

