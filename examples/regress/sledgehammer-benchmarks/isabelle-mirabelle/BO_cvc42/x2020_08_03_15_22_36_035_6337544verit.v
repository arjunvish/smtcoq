Add Rec LoadPath "../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test15.
  Goal True. idtac "". idtac "isabelle-mirabelle/BO_cvc42/x2020_08_03_15_22_36_035_6337544verit.v". Abort.
  Verit_Checker "x2020_08_03_15_22_36_035_6337544.smt_in" "x2020_08_03_15_22_36_035_6337544.smt_inproofnew".
End test15.

