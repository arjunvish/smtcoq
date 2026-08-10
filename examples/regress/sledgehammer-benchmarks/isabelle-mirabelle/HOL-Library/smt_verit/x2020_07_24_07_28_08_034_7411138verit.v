Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test49.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_verit/x2020_07_24_07_28_08_034_7411138verit.v". Abort.
  Verit_Checker "x2020_07_24_07_28_08_034_7411138.smt_in" "x2020_07_24_07_28_08_034_7411138.smt_inproofnew".
End test49.

