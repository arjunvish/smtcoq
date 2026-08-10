Add Rec LoadPath "../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test91.
  Goal True. idtac "". idtac "isabelle-mirabelle/PNT_cvc42/x2020_08_04_17_34_35_557_9411026.v". Abort.
  Verit_Checker "x2020_08_04_17_34_35_557_9411026.smt_in" "x2020_08_04_17_34_35_557_9411026.smt_inproofnew".
End test91.
