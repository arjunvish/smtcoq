Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test76.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_cvc4/x2020_07_23_15_23_16_143_4983100verit.v". Abort.
  Verit_Checker "x2020_07_23_15_23_16_143_4983100.smt_in" "x2020_07_23_15_23_16_143_4983100.smt_inproofnew".
End test76.

