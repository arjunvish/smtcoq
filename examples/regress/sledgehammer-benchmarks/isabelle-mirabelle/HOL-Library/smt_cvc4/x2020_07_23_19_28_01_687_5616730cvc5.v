Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test67.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_cvc4/x2020_07_23_19_28_01_687_5616730cvc5.v". Abort.
  Verit_Checker "x2020_07_23_19_28_01_687_5616730.smt_in" "x2020_07_23_19_28_01_687_5616730.cvc5oldpf".
End test67.

