Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test110.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_29_04_22_19_856_8862020verit.v". Abort.
  Verit_Checker "x2020_07_29_04_22_19_856_8862020.smt_in" "x2020_07_29_04_22_19_856_8862020.smt_inproofnew".
End test110.

