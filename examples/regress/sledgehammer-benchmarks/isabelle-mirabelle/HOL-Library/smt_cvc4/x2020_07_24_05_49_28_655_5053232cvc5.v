Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test79.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_cvc4/x2020_07_24_05_49_28_655_5053232cvc5.v". Abort.
  Verit_Checker "x2020_07_24_05_49_28_655_5053232.smt_in" "x2020_07_24_05_49_28_655_5053232.cvc5oldpf".
End test79.

