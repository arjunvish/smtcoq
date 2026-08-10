Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test140.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_28_21_17_40_281_7539822cvc5.v". Abort.
  Verit_Checker "x2020_07_28_21_17_40_281_7539822.smt_in" "x2020_07_28_21_17_40_281_7539822.cvc5oldpf".
End test140.

