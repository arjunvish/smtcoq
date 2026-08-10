Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test122.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_28_22_03_52_352_5382930verit.v". Abort.
  Verit_Checker "x2020_07_28_22_03_52_352_5382930.smt_in" "x2020_07_28_22_03_52_352_5382930.smt_inproofnew".
End test122.

