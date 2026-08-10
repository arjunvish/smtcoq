Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test83.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_cvc4/x2020_07_23_23_22_38_994_4983000verit.v". Abort.
  Verit_Checker "x2020_07_23_23_22_38_994_4983000.smt_in" "x2020_07_23_23_22_38_994_4983000.smt_inproofnew".
End test83.

