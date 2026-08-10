Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test122.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_29_03_31_01_486_8397120.v". Abort.
  Verit_Checker "x2020_07_29_03_31_01_486_8397120.smt_in" "x2020_07_29_03_31_01_486_8397120.smt_inproofnew".
End test122.
