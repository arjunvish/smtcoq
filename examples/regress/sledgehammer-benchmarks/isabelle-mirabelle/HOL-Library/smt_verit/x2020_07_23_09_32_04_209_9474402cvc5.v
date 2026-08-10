Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test61.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_verit/x2020_07_23_09_32_04_209_9474402cvc5.v". Abort.
  Verit_Checker "x2020_07_23_09_32_04_209_9474402.smt_in" "x2020_07_23_09_32_04_209_9474402.cvc5oldpf".
End test61.

