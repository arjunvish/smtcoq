Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test66.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_verit/x2020_07_23_09_28_18_949_9432688.v". Abort.
  Verit_Checker "x2020_07_23_09_28_18_949_9432688.smt_in" "x2020_07_23_09_28_18_949_9432688.smt_inproofnew".
End test66.
