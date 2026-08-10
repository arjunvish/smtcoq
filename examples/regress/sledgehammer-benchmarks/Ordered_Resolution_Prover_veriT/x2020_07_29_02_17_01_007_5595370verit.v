Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test143.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_29_02_17_01_007_5595370verit.v". Abort.
  Verit_Checker "x2020_07_29_02_17_01_007_5595370.smt_in" "x2020_07_29_02_17_01_007_5595370.smt_inproofnew".
End test143.

