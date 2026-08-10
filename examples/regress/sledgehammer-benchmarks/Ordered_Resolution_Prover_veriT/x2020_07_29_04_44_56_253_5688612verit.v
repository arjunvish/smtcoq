Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test102.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_29_04_44_56_253_5688612verit.v". Abort.
  Verit_Checker "x2020_07_29_04_44_56_253_5688612.smt_in" "x2020_07_29_04_44_56_253_5688612.smt_inproofnew".
End test102.

