Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test84.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_cvc4/x2020_07_24_01_29_51_707_5106282verit.v". Abort.
  Verit_Checker "x2020_07_24_01_29_51_707_5106282.smt_in" "x2020_07_24_01_29_51_707_5106282.smt_inproofnew".
End test84.

