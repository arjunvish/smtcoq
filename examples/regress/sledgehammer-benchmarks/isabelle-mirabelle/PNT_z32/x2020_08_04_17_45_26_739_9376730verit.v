Add Rec LoadPath "../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test3.
  Goal True. idtac "". idtac "isabelle-mirabelle/PNT_z32/x2020_08_04_17_45_26_739_9376730verit.v". Abort.
  Verit_Checker "x2020_08_04_17_45_26_739_9376730.smt_in" "x2020_08_04_17_45_26_739_9376730.smt_inproofnew".
End test3.

