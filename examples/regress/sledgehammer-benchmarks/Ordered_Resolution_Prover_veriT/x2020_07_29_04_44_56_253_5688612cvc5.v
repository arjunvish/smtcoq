Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test100.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_29_04_44_56_253_5688612cvc5.v". Abort.
  Verit_Checker "x2020_07_29_04_44_56_253_5688612.smt_in" "x2020_07_29_04_44_56_253_5688612.cvc5oldpf".
End test100.

