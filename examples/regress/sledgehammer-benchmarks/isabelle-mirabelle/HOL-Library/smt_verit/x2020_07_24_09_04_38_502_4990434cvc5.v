Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test52.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_verit/x2020_07_24_09_04_38_502_4990434cvc5.v". Abort.
  Verit_Checker "x2020_07_24_09_04_38_502_4990434.smt_in" "x2020_07_24_09_04_38_502_4990434.cvc5oldpf".
End test52.

