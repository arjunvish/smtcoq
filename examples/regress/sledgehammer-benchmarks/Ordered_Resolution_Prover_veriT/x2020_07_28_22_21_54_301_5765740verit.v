Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test100.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_28_22_21_54_301_5765740verit.v". Abort.
  Verit_Checker "x2020_07_28_22_21_54_301_5765740.smt_in" "x2020_07_28_22_21_54_301_5765740.smt_inproofnew".
End test100.

