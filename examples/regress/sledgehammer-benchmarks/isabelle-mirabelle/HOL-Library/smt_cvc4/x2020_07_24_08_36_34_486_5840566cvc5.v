Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test80.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_cvc4/x2020_07_24_08_36_34_486_5840566cvc5.v". Abort.
  Verit_Checker "x2020_07_24_08_36_34_486_5840566.smt_in" "x2020_07_24_08_36_34_486_5840566.cvc5oldpf".
End test80.

