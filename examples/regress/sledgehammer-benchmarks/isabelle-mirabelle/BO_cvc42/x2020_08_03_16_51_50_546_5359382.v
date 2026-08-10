Add Rec LoadPath "../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test5.
  Goal True. idtac "". idtac "isabelle-mirabelle/BO_cvc42/x2020_08_03_16_51_50_546_5359382.v". Abort.
  Verit_Checker "x2020_08_03_16_51_50_546_5359382.smt_in" "x2020_08_03_16_51_50_546_5359382.smt_inproofnew".
End test5.
