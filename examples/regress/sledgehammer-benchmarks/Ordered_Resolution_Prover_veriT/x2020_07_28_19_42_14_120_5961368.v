Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test94.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_28_19_42_14_120_5961368.v". Abort.
  Verit_Checker "x2020_07_28_19_42_14_120_5961368.smt_in" "x2020_07_28_19_42_14_120_5961368.smt_inproofnew".
End test94.
