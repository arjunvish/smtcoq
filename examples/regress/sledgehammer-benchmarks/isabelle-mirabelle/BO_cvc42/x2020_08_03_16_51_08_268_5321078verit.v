Add Rec LoadPath "../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test17.
  Goal True. idtac "". idtac "isabelle-mirabelle/BO_cvc42/x2020_08_03_16_51_08_268_5321078verit.v". Abort.
  Verit_Checker "x2020_08_03_16_51_08_268_5321078.smt_in" "x2020_08_03_16_51_08_268_5321078.smt_inproofnew".
End test17.

