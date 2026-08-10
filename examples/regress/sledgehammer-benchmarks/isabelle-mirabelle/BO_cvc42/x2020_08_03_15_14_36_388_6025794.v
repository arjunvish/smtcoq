Add Rec LoadPath "../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test18.
  Goal True. idtac "". idtac "isabelle-mirabelle/BO_cvc42/x2020_08_03_15_14_36_388_6025794.v". Abort.
  Verit_Checker "x2020_08_03_15_14_36_388_6025794.smt_in" "x2020_08_03_15_14_36_388_6025794.smt_inproofnew".
End test18.
