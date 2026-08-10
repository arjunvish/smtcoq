Add Rec LoadPath "../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test18.
  Goal True. idtac "". idtac "isabelle-mirabelle/BO_cvc42/x2020_08_03_17_08_43_615_6004000verit.v". Abort.
  Verit_Checker "x2020_08_03_17_08_43_615_6004000.smt_in" "x2020_08_03_17_08_43_615_6004000.smt_inproofnew".
End test18.

