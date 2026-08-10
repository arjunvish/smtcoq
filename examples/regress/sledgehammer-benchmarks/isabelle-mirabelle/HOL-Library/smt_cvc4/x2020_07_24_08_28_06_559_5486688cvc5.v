Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test85.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_cvc4/x2020_07_24_08_28_06_559_5486688cvc5.v". Abort.
  Verit_Checker "x2020_07_24_08_28_06_559_5486688.smt_in" "x2020_07_24_08_28_06_559_5486688.cvc5oldpf".
End test85.

