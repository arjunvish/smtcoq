Add Rec LoadPath "../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test3.
  Goal True. idtac "". idtac "isabelle-mirabelle/BO_cvc42/x2020_08_03_16_00_26_055_7846716cvc5.v". Abort.
  Verit_Checker "x2020_08_03_16_00_26_055_7846716.smt_in" "x2020_08_03_16_00_26_055_7846716.cvc5oldpf".
End test3.

