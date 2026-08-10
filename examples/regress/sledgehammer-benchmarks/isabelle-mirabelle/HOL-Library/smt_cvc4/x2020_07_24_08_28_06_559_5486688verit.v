Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test87.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_cvc4/x2020_07_24_08_28_06_559_5486688verit.v". Abort.
  Verit_Checker "x2020_07_24_08_28_06_559_5486688.smt_in" "x2020_07_24_08_28_06_559_5486688.smt_inproofnew".
End test87.

