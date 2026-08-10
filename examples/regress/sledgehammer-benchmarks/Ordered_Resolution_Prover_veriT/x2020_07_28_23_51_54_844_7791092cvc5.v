Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test105.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_28_23_51_54_844_7791092cvc5.v". Abort.
  Verit_Checker "x2020_07_28_23_51_54_844_7791092.smt_in" "x2020_07_28_23_51_54_844_7791092.cvc5oldpf".
End test105.

