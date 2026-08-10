Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test51.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_verit/x2020_07_23_14_32_04_464_17993960cvc5.v". Abort.
  Verit_Checker "x2020_07_23_14_32_04_464_17993960.smt_in" "x2020_07_23_14_32_04_464_17993960.cvc5oldpf".
End test51.

