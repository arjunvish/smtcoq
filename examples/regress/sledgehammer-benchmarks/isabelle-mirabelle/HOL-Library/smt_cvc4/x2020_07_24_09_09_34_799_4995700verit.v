Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test78.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_cvc4/x2020_07_24_09_09_34_799_4995700verit.v". Abort.
  Verit_Checker "x2020_07_24_09_09_34_799_4995700.smt_in" "x2020_07_24_09_09_34_799_4995700.smt_inproofnew".
End test78.

