Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test44.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_verit/x2020_07_24_02_50_45_899_5005750verit.v". Abort.
  Verit_Checker "x2020_07_24_02_50_45_899_5005750.smt_in" "x2020_07_24_02_50_45_899_5005750.smt_inproofnew".
End test44.

