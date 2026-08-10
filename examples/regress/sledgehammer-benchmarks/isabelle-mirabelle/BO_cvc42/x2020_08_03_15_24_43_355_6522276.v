Add Rec LoadPath "../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test6.
  Goal True. idtac "". idtac "isabelle-mirabelle/BO_cvc42/x2020_08_03_15_24_43_355_6522276.v". Abort.
  Verit_Checker "x2020_08_03_15_24_43_355_6522276.smt_in" "x2020_08_03_15_24_43_355_6522276.smt_inproofnew".
End test6.
