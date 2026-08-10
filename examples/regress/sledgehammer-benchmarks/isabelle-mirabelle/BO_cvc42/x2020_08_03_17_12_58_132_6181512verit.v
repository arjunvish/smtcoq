Add Rec LoadPath "../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test13.
  Goal True. idtac "". idtac "isabelle-mirabelle/BO_cvc42/x2020_08_03_17_12_58_132_6181512verit.v". Abort.
  Verit_Checker "x2020_08_03_17_12_58_132_6181512.smt_in" "x2020_08_03_17_12_58_132_6181512.smt_inproofnew".
End test13.

