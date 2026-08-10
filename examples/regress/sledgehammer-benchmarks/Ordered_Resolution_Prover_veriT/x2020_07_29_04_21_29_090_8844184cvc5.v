Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test121.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_29_04_21_29_090_8844184cvc5.v". Abort.
  Verit_Checker "x2020_07_29_04_21_29_090_8844184.smt_in" "x2020_07_29_04_21_29_090_8844184.cvc5oldpf".
End test121.

