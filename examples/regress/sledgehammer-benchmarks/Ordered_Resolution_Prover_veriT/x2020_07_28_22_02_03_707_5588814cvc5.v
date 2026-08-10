Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test135.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_28_22_02_03_707_5588814cvc5.v". Abort.
  Verit_Checker "x2020_07_28_22_02_03_707_5588814.smt_in" "x2020_07_28_22_02_03_707_5588814.cvc5oldpf".
End test135.

