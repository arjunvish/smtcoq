Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test57.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_verit/x2020_07_23_15_16_51_570_4983100verit.v". Abort.
  Verit_Checker "x2020_07_23_15_16_51_570_4983100.smt_in" "x2020_07_23_15_16_51_570_4983100.smt_inproofnew".
End test57.

