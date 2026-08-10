Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test66.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_verit/x2020_07_23_14_32_00_883_17987914verit.v". Abort.
  Verit_Checker "x2020_07_23_14_32_00_883_17987914.smt_in" "x2020_07_23_14_32_00_883_17987914.smt_inproofnew".
End test66.

