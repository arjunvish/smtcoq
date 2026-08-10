Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test105.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_29_04_18_11_899_8806006verit.v". Abort.
  Verit_Checker "x2020_07_29_04_18_11_899_8806006.smt_in" "x2020_07_29_04_18_11_899_8806006.smt_inproofnew".
End test105.

