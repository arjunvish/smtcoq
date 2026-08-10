Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test89.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_cvc4/x2020_07_24_05_49_32_934_5066708verit.v". Abort.
  Verit_Checker "x2020_07_24_05_49_32_934_5066708.smt_in" "x2020_07_24_05_49_32_934_5066708.smt_inproofnew".
End test89.

