Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test137.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_28_22_02_03_707_5588814verit.v". Abort.
  Verit_Checker "x2020_07_28_22_02_03_707_5588814.smt_in" "x2020_07_28_22_02_03_707_5588814.smt_inproofnew".
End test137.

