Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test71.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_cvc4/x2020_07_24_09_13_44_183_5157124verit.v". Abort.
  Verit_Checker "x2020_07_24_09_13_44_183_5157124.smt_in" "x2020_07_24_09_13_44_183_5157124.smt_inproofnew".
End test71.

