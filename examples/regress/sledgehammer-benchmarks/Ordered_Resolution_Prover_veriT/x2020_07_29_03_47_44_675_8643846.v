Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test109.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_29_03_47_44_675_8643846.v". Abort.
  Verit_Checker "x2020_07_29_03_47_44_675_8643846.smt_in" "x2020_07_29_03_47_44_675_8643846.smt_inproofnew".
End test109.
