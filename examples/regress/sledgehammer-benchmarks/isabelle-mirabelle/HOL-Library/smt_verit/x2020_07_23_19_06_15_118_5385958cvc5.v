Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test53.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_verit/x2020_07_23_19_06_15_118_5385958cvc5.v". Abort.
  Verit_Checker "x2020_07_23_19_06_15_118_5385958.smt_in" "x2020_07_23_19_06_15_118_5385958.cvc5oldpf".
End test53.

