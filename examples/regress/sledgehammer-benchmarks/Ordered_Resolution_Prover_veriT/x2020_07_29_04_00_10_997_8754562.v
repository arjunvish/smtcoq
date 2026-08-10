Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test123.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_29_04_00_10_997_8754562.v". Abort.
  Verit_Checker "x2020_07_29_04_00_10_997_8754562.smt_in" "x2020_07_29_04_00_10_997_8754562.smt_inproofnew".
End test123.
