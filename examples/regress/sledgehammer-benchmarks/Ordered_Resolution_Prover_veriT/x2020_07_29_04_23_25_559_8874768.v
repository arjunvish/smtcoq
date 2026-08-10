Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test125.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_29_04_23_25_559_8874768.v". Abort.
  Verit_Checker "x2020_07_29_04_23_25_559_8874768.smt_in" "x2020_07_29_04_23_25_559_8874768.smt_inproofnew".
End test125.
