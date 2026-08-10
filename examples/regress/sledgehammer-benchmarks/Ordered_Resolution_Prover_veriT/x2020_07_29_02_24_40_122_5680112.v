Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test113.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_29_02_24_40_122_5680112.v". Abort.
  Verit_Checker "x2020_07_29_02_24_40_122_5680112.smt_in" "x2020_07_29_02_24_40_122_5680112.smt_inproofnew".
End test113.
