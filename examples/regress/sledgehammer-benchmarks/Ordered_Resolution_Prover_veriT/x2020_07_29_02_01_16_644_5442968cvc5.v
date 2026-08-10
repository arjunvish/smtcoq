Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test114.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_29_02_01_16_644_5442968cvc5.v". Abort.
  Verit_Checker "x2020_07_29_02_01_16_644_5442968.smt_in" "x2020_07_29_02_01_16_644_5442968.cvc5oldpf".
End test114.

