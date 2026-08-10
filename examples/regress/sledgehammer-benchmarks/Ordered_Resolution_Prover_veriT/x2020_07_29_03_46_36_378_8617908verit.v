Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test95.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_29_03_46_36_378_8617908verit.v". Abort.
  Verit_Checker "x2020_07_29_03_46_36_378_8617908.smt_in" "x2020_07_29_03_46_36_378_8617908.smt_inproofnew".
End test95.

