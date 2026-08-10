Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test71.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_cvc4/x2020_07_24_08_38_00_870_5908880cvc5.v". Abort.
  Verit_Checker "x2020_07_24_08_38_00_870_5908880.smt_in" "x2020_07_24_08_38_00_870_5908880.cvc5oldpf".
End test71.

