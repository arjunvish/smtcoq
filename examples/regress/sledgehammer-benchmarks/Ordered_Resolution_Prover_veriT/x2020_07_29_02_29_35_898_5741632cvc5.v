Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test95.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_29_02_29_35_898_5741632cvc5.v". Abort.
  Verit_Checker "x2020_07_29_02_29_35_898_5741632.smt_in" "x2020_07_29_02_29_35_898_5741632.cvc5oldpf".
End test95.

