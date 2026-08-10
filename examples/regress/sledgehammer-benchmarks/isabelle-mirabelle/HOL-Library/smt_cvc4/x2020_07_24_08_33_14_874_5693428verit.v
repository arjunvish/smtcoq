Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test74.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_cvc4/x2020_07_24_08_33_14_874_5693428verit.v". Abort.
  Verit_Checker "x2020_07_24_08_33_14_874_5693428.smt_in" "x2020_07_24_08_33_14_874_5693428.smt_inproofnew".
End test74.

