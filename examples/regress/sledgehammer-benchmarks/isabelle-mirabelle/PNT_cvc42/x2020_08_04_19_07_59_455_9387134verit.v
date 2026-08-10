Add Rec LoadPath "../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test94.
  Goal True. idtac "". idtac "isabelle-mirabelle/PNT_cvc42/x2020_08_04_19_07_59_455_9387134verit.v". Abort.
  Verit_Checker "x2020_08_04_19_07_59_455_9387134.smt_in" "x2020_08_04_19_07_59_455_9387134.smt_inproofnew".
End test94.

