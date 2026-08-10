Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test131.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_28_21_52_48_419_6580796verit.v". Abort.
  Verit_Checker "x2020_07_28_21_52_48_419_6580796.smt_in" "x2020_07_28_21_52_48_419_6580796.smt_inproofnew".
End test131.

