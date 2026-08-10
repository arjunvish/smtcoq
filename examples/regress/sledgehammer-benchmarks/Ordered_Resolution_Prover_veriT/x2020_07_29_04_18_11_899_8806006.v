Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test103.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_29_04_18_11_899_8806006.v". Abort.
  Verit_Checker "x2020_07_29_04_18_11_899_8806006.smt_in" "x2020_07_29_04_18_11_899_8806006.smt_inproofnew".
End test103.
