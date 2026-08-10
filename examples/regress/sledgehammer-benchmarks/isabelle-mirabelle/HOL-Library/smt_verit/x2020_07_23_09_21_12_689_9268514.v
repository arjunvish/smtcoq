Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test29.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_verit/x2020_07_23_09_21_12_689_9268514.v". Abort.
  Verit_Checker "x2020_07_23_09_21_12_689_9268514.smt_in" "x2020_07_23_09_21_12_689_9268514.smt_inproofnew".
End test29.
