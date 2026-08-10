Add Rec LoadPath "../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test22.
  Goal True. idtac "". idtac "isabelle-mirabelle/BO_cvc42/x2020_08_03_15_23_49_010_6452792verit.v". Abort.
  Verit_Checker "x2020_08_03_15_23_49_010_6452792.smt_in" "x2020_08_03_15_23_49_010_6452792.smt_inproofnew".
End test22.

