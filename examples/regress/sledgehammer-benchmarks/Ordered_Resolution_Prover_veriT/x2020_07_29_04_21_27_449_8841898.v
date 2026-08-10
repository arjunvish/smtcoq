Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test119.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_29_04_21_27_449_8841898.v". Abort.
  Verit_Checker "x2020_07_29_04_21_27_449_8841898.smt_in" "x2020_07_29_04_21_27_449_8841898.smt_inproofnew".
End test119.
