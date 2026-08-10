Add Rec LoadPath "../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test9.
  Goal True. idtac "". idtac "isabelle-mirabelle/BO_cvc42/x2020_08_03_17_15_27_694_6279318cvc5.v". Abort.
  Verit_Checker "x2020_08_03_17_15_27_694_6279318.smt_in" "x2020_08_03_17_15_27_694_6279318.cvc5oldpf".
End test9.

