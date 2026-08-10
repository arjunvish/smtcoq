Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test108.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_29_03_33_34_830_8439854verit.v". Abort.
  Verit_Checker "x2020_07_29_03_33_34_830_8439854.smt_in" "x2020_07_29_03_33_34_830_8439854.smt_inproofnew".
End test108.

