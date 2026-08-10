Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test123.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_29_04_21_29_090_8844184verit.v". Abort.
  Verit_Checker "x2020_07_29_04_21_29_090_8844184.smt_in" "x2020_07_29_04_21_29_090_8844184.smt_inproofnew".
End test123.

