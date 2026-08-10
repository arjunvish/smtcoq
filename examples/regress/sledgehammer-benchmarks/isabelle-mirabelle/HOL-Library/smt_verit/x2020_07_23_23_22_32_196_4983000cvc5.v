Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test31.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_verit/x2020_07_23_23_22_32_196_4983000cvc5.v". Abort.
  Verit_Checker "x2020_07_23_23_22_32_196_4983000.smt_in" "x2020_07_23_23_22_32_196_4983000.cvc5oldpf".
End test31.

