Add Rec LoadPath "../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test16.
  Goal True. idtac "". idtac "isabelle-mirabelle/BO_cvc42/x2020_08_03_15_24_49_644_6536112verit.v". Abort.
  Verit_Checker "x2020_08_03_15_24_49_644_6536112.smt_in" "x2020_08_03_15_24_49_644_6536112.smt_inproofnew".
End test16.

