Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test59.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_verit/x2020_07_23_18_51_42_656_5093812verit.v". Abort.
  Verit_Checker "x2020_07_23_18_51_42_656_5093812.smt_in" "x2020_07_23_18_51_42_656_5093812.smt_inproofnew".
End test59.

