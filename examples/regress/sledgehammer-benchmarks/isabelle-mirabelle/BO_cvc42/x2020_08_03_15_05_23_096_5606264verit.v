Add Rec LoadPath "../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test4.
  Goal True. idtac "". idtac "isabelle-mirabelle/BO_cvc42/x2020_08_03_15_05_23_096_5606264verit.v". Abort.
  Verit_Checker "x2020_08_03_15_05_23_096_5606264.smt_in" "x2020_08_03_15_05_23_096_5606264.smt_inproofnew".
End test4.

