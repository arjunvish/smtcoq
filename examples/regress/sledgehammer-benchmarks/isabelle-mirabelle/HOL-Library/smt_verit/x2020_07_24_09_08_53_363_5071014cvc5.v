Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test62.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_verit/x2020_07_24_09_08_53_363_5071014cvc5.v". Abort.
  Verit_Checker "x2020_07_24_09_08_53_363_5071014.smt_in" "x2020_07_24_09_08_53_363_5071014.cvc5oldpf".
End test62.

