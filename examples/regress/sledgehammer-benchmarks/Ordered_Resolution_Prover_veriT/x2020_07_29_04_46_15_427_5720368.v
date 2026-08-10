Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test116.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_29_04_46_15_427_5720368.v". Abort.
  Verit_Checker "x2020_07_29_04_46_15_427_5720368.smt_in" "x2020_07_29_04_46_15_427_5720368.smt_inproofnew".
End test116.
