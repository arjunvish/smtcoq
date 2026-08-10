Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test75.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_cvc4/x2020_07_23_19_31_32_094_5725034verit.v". Abort.
  Verit_Checker "x2020_07_23_19_31_32_094_5725034.smt_in" "x2020_07_23_19_31_32_094_5725034.smt_inproofnew".
End test75.

