Add Rec LoadPath "../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test1.
  Goal True. idtac "". idtac "isabelle-mirabelle/PNT_z32/x2020_08_04_17_45_26_739_9376730cvc5.v". Abort.
  Verit_Checker "x2020_08_04_17_45_26_739_9376730.smt_in" "x2020_08_04_17_45_26_739_9376730.cvc5oldpf".
End test1.

