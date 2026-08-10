Add Rec LoadPath "../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test27.
  Goal True. idtac "". idtac "isabelle-mirabelle/BO_cvc42/x2020_08_03_15_56_39_113_7636710verit.v". Abort.
  Verit_Checker "x2020_08_03_15_56_39_113_7636710.smt_in" "x2020_08_03_15_56_39_113_7636710.smt_inproofnew".
End test27.

