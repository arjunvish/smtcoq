Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test72.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_cvc4/x2020_07_23_19_13_29_740_5029568verit.v". Abort.
  Verit_Checker "x2020_07_23_19_13_29_740_5029568.smt_in" "x2020_07_23_19_13_29_740_5029568.smt_inproofnew".
End test72.

