Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test33.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_verit/x2020_07_23_23_22_32_196_4983000verit.v". Abort.
  Verit_Checker "x2020_07_23_23_22_32_196_4983000.smt_in" "x2020_07_23_23_22_32_196_4983000.smt_inproofnew".
End test33.

