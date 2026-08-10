Add Rec LoadPath "../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test13.
  Goal True. idtac "". idtac "isabelle-mirabelle/BO_cvc42/x2020_08_03_15_22_36_035_6337544cvc5.v". Abort.
  Verit_Checker "x2020_08_03_15_22_36_035_6337544.smt_in" "x2020_08_03_15_22_36_035_6337544.cvc5oldpf".
End test13.

