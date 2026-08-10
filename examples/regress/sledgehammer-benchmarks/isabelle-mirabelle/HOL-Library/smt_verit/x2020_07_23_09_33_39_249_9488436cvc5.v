Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test33.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_verit/x2020_07_23_09_33_39_249_9488436cvc5.v". Abort.
  Verit_Checker "x2020_07_23_09_33_39_249_9488436.smt_in" "x2020_07_23_09_33_39_249_9488436.cvc5oldpf".
End test33.

