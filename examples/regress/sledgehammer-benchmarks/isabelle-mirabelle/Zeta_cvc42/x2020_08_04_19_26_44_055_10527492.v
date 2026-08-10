Add Rec LoadPath "../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test90.
  Goal True. idtac "". idtac "isabelle-mirabelle/Zeta_cvc42/x2020_08_04_19_26_44_055_10527492.v". Abort.
  Verit_Checker "x2020_08_04_19_26_44_055_10527492.smt_in" "x2020_08_04_19_26_44_055_10527492.smt_inproofnew".
End test90.
