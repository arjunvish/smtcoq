Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test134.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_29_04_36_57_199_5464880cvc5.v". Abort.
  Verit_Checker "x2020_07_29_04_36_57_199_5464880.smt_in" "x2020_07_29_04_36_57_199_5464880.cvc5oldpf".
End test134.

