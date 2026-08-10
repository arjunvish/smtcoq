Add Rec LoadPath "../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test5.
  Goal True. idtac "". idtac "isabelle-mirabelle/BO_cvc42/x2020_08_03_16_00_26_055_7846716verit.v". Abort.
  Verit_Checker "x2020_08_03_16_00_26_055_7846716.smt_in" "x2020_08_03_16_00_26_055_7846716.smt_inproofnew".
End test5.

