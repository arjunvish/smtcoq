Add Rec LoadPath "../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test12.
  Goal True. idtac "". idtac "isabelle-mirabelle/BO_cvc42/x2020_08_03_16_40_35_239_4899098verit.v". Abort.
  Verit_Checker "x2020_08_03_16_40_35_239_4899098.smt_in" "x2020_08_03_16_40_35_239_4899098.smt_inproofnew".
End test12.

