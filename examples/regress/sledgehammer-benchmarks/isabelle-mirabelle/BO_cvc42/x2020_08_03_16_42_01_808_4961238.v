Add Rec LoadPath "../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test17.
  Goal True. idtac "". idtac "isabelle-mirabelle/BO_cvc42/x2020_08_03_16_42_01_808_4961238.v". Abort.
  Verit_Checker "x2020_08_03_16_42_01_808_4961238.smt_in" "x2020_08_03_16_42_01_808_4961238.smt_inproofnew".
End test17.
