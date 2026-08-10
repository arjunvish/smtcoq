Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test32.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_verit/x2020_07_23_19_10_14_273_5442982cvc5.v". Abort.
  Verit_Checker "x2020_07_23_19_10_14_273_5442982.smt_in" "x2020_07_23_19_10_14_273_5442982.cvc5oldpf".
End test32.

