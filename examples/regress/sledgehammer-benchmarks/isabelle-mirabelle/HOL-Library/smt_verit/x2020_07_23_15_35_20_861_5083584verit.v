Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test56.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_verit/x2020_07_23_15_35_20_861_5083584verit.v". Abort.
  Verit_Checker "x2020_07_23_15_35_20_861_5083584.smt_in" "x2020_07_23_15_35_20_861_5083584.smt_inproofnew".
End test56.

