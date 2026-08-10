Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test125.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_29_04_00_10_997_8754562verit.v". Abort.
  Verit_Checker "x2020_07_29_04_00_10_997_8754562.smt_in" "x2020_07_29_04_00_10_997_8754562.smt_inproofnew".
End test125.

