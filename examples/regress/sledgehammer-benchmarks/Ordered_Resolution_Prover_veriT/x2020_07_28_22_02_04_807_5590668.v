Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test126.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_28_22_02_04_807_5590668.v". Abort.
  Verit_Checker "x2020_07_28_22_02_04_807_5590668.smt_in" "x2020_07_28_22_02_04_807_5590668.smt_inproofnew".
End test126.
