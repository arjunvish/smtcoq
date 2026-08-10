Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test48.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_verit/x2020_07_24_07_48_19_224_8437724cvc5.v". Abort.
  Verit_Checker "x2020_07_24_07_48_19_224_8437724.smt_in" "x2020_07_24_07_48_19_224_8437724.cvc5oldpf".
End test48.

