Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test110.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_29_00_24_03_784_9778214.v". Abort.
  Verit_Checker "x2020_07_29_00_24_03_784_9778214.smt_in" "x2020_07_29_00_24_03_784_9778214.smt_inproofnew".
End test110.
