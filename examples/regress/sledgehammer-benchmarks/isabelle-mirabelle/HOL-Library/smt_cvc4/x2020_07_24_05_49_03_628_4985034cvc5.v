Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test88.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_cvc4/x2020_07_24_05_49_03_628_4985034cvc5.v". Abort.
  Verit_Checker "x2020_07_24_05_49_03_628_4985034.smt_in" "x2020_07_24_05_49_03_628_4985034.cvc5oldpf".
End test88.

