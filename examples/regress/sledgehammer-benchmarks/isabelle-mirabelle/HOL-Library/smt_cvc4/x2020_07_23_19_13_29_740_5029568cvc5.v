Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test70.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_cvc4/x2020_07_23_19_13_29_740_5029568cvc5.v". Abort.
  Verit_Checker "x2020_07_23_19_13_29_740_5029568.smt_in" "x2020_07_23_19_13_29_740_5029568.cvc5oldpf".
End test70.

