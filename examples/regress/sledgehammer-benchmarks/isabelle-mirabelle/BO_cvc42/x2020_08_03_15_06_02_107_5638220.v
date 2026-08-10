Add Rec LoadPath "../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test19.
  Goal True. idtac "". idtac "isabelle-mirabelle/BO_cvc42/x2020_08_03_15_06_02_107_5638220.v". Abort.
  Verit_Checker "x2020_08_03_15_06_02_107_5638220.smt_in" "x2020_08_03_15_06_02_107_5638220.smt_inproofnew".
End test19.
