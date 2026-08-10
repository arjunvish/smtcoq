Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test141.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_29_01_40_12_306_5528196verit.v". Abort.
  Verit_Checker "x2020_07_29_01_40_12_306_5528196.smt_in" "x2020_07_29_01_40_12_306_5528196.smt_inproofnew".
End test141.

