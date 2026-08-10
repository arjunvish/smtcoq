Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test127.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_28_22_01_57_407_5584508cvc5.v". Abort.
  Verit_Checker "x2020_07_28_22_01_57_407_5584508.smt_in" "x2020_07_28_22_01_57_407_5584508.cvc5oldpf".
End test127.

