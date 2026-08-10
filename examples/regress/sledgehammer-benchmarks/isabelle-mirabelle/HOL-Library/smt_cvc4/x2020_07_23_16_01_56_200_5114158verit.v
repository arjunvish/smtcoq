Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test88.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_cvc4/x2020_07_23_16_01_56_200_5114158verit.v". Abort.
  Verit_Checker "x2020_07_23_16_01_56_200_5114158.smt_in" "x2020_07_23_16_01_56_200_5114158.smt_inproofnew".
End test88.

