Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test99.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_28_21_17_42_834_7543784.v". Abort.
  Verit_Checker "x2020_07_28_21_17_42_834_7543784.smt_in" "x2020_07_28_21_17_42_834_7543784.smt_inproofnew".
End test99.
