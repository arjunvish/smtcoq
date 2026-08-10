Add Rec LoadPath "../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test4.
  Goal True. idtac "". idtac "isabelle-mirabelle/BO_cvc42/x2020_08_03_16_50_04_968_5248672.v". Abort.
  Verit_Checker "x2020_08_03_16_50_04_968_5248672.smt_in" "x2020_08_03_16_50_04_968_5248672.smt_inproofnew".
End test4.
