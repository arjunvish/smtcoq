Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test129.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_28_22_01_57_407_5584508verit.v". Abort.
  Verit_Checker "x2020_07_28_22_01_57_407_5584508.smt_in" "x2020_07_28_22_01_57_407_5584508.smt_inproofnew".
End test129.

