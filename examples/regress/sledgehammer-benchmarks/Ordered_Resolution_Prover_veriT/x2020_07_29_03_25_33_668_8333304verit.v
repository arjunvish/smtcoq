Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test126.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_29_03_25_33_668_8333304verit.v". Abort.
  Verit_Checker "x2020_07_29_03_25_33_668_8333304.smt_in" "x2020_07_29_03_25_33_668_8333304.smt_inproofnew".
End test126.

