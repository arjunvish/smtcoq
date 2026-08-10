Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test38.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_verit/x2020_07_23_15_39_12_904_5134392.v". Abort.
  Verit_Checker "x2020_07_23_15_39_12_904_5134392.smt_in" "x2020_07_23_15_39_12_904_5134392.smt_inproofnew".
End test38.
