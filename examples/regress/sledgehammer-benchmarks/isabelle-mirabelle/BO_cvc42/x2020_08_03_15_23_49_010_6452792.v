Add Rec LoadPath "../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test20.
  Goal True. idtac "". idtac "isabelle-mirabelle/BO_cvc42/x2020_08_03_15_23_49_010_6452792.v". Abort.
  Verit_Checker "x2020_08_03_15_23_49_010_6452792.smt_in" "x2020_08_03_15_23_49_010_6452792.smt_inproofnew".
End test20.
