Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test32.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_verit/x2020_07_24_07_41_03_832_8304788verit.v". Abort.
  Verit_Checker "x2020_07_24_07_41_03_832_8304788.smt_in" "x2020_07_24_07_41_03_832_8304788.smt_inproofnew".
End test32.

