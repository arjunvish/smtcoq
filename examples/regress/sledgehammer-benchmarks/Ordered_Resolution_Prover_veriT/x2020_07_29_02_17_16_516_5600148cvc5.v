Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test138.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_29_02_17_16_516_5600148cvc5.v". Abort.
  Verit_Checker "x2020_07_29_02_17_16_516_5600148.smt_in" "x2020_07_29_02_17_16_516_5600148.cvc5oldpf".
End test138.

