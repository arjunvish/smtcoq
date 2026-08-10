Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test81.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_cvc4/x2020_07_23_23_22_38_994_4983000cvc5.v". Abort.
  Verit_Checker "x2020_07_23_23_22_38_994_4983000.smt_in" "x2020_07_23_23_22_38_994_4983000.cvc5oldpf".
End test81.

