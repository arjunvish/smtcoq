Add Rec LoadPath "../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test29.
  Goal True. idtac "". idtac "isabelle-mirabelle/BO_cvc42/x2020_08_03_16_50_48_855_5281470verit.v". Abort.
  Verit_Checker "x2020_08_03_16_50_48_855_5281470.smt_in" "x2020_08_03_16_50_48_855_5281470.smt_inproofnew".
End test29.

