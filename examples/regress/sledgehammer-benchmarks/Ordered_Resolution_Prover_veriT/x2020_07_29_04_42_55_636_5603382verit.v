Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test132.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_29_04_42_55_636_5603382verit.v". Abort.
  Verit_Checker "x2020_07_29_04_42_55_636_5603382.smt_in" "x2020_07_29_04_42_55_636_5603382.smt_inproofnew".
End test132.

