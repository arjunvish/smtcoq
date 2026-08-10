Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test84.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_cvc4/x2020_07_23_19_16_11_074_5147710.v". Abort.
  Verit_Checker "x2020_07_23_19_16_11_074_5147710.smt_in" "x2020_07_23_19_16_11_074_5147710.smt_inproofnew".
End test84.
