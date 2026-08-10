Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test35.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_verit/x2020_07_23_09_33_39_249_9488436verit.v". Abort.
  Verit_Checker "x2020_07_23_09_33_39_249_9488436.smt_in" "x2020_07_23_09_33_39_249_9488436.smt_inproofnew".
End test35.

