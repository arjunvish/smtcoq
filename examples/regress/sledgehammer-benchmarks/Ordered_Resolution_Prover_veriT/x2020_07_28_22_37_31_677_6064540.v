Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test115.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_28_22_37_31_677_6064540.v". Abort.
  Verit_Checker "x2020_07_28_22_37_31_677_6064540.smt_in" "x2020_07_28_22_37_31_677_6064540.smt_inproofnew".
End test115.
