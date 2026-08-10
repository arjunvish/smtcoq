Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test114.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_28_23_31_31_371_7343286verit.v". Abort.
  Verit_Checker "x2020_07_28_23_31_31_371_7343286.smt_in" "x2020_07_28_23_31_31_371_7343286.smt_inproofnew".
End test114.

