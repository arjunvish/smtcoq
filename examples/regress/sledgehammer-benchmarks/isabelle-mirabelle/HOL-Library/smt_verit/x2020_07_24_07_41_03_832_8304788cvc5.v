Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test30.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_verit/x2020_07_24_07_41_03_832_8304788cvc5.v". Abort.
  Verit_Checker "x2020_07_24_07_41_03_832_8304788.smt_in" "x2020_07_24_07_41_03_832_8304788.cvc5oldpf".
End test30.

