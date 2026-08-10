Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test43.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_verit/x2020_07_24_09_09_13_580_5081634cvc5.v". Abort.
  Verit_Checker "x2020_07_24_09_09_13_580_5081634.smt_in" "x2020_07_24_09_09_13_580_5081634.cvc5oldpf".
End test43.

