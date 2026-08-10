Add Rec LoadPath "../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test91.
  Goal True. idtac "". idtac "isabelle-mirabelle/Green_cvc42/x2020_07_31_07_55_13_484_7016530verit.v". Abort.
  Verit_Checker "x2020_07_31_07_55_13_484_7016530.smt_in" "x2020_07_31_07_55_13_484_7016530.smt_inproofnew".
End test91.

