Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test41.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_verit/x2020_07_23_18_47_51_743_5021316cvc5.v". Abort.
  Verit_Checker "x2020_07_23_18_47_51_743_5021316.smt_in" "x2020_07_23_18_47_51_743_5021316.cvc5oldpf".
End test41.

