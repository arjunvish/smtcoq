Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test97.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_28_22_19_53_992_5730614.v". Abort.
  Verit_Checker "x2020_07_28_22_19_53_992_5730614.smt_in" "x2020_07_28_22_19_53_992_5730614.smt_inproofnew".
End test97.
