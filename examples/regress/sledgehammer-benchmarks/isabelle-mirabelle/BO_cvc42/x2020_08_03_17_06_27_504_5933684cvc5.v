Add Rec LoadPath "../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test8.
  Goal True. idtac "". idtac "isabelle-mirabelle/BO_cvc42/x2020_08_03_17_06_27_504_5933684cvc5.v". Abort.
  Verit_Checker "x2020_08_03_17_06_27_504_5933684.smt_in" "x2020_08_03_17_06_27_504_5933684.cvc5oldpf".
End test8.

