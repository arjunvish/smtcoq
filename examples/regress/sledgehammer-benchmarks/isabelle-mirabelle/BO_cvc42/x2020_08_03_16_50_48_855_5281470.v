Add Rec LoadPath "../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test27.
  Goal True. idtac "". idtac "isabelle-mirabelle/BO_cvc42/x2020_08_03_16_50_48_855_5281470.v". Abort.
  Verit_Checker "x2020_08_03_16_50_48_855_5281470.smt_in" "x2020_08_03_16_50_48_855_5281470.smt_inproofnew".
End test27.
