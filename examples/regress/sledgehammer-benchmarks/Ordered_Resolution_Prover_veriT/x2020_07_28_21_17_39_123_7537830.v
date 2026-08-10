Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test101.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_28_21_17_39_123_7537830.v". Abort.
  Verit_Checker "x2020_07_28_21_17_39_123_7537830.smt_in" "x2020_07_28_21_17_39_123_7537830.smt_inproofnew".
End test101.
