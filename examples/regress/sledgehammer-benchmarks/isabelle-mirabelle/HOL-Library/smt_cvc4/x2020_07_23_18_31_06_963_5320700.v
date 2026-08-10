Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test78.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_cvc4/x2020_07_23_18_31_06_963_5320700.v". Abort.
  Verit_Checker "x2020_07_23_18_31_06_963_5320700.smt_in" "x2020_07_23_18_31_06_963_5320700.smt_inproofnew".
End test78.
