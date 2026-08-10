Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test98.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_28_21_17_43_975_7545750verit.v". Abort.
  Verit_Checker "x2020_07_28_21_17_43_975_7545750.smt_in" "x2020_07_28_21_17_43_975_7545750.smt_inproofnew".
End test98.

