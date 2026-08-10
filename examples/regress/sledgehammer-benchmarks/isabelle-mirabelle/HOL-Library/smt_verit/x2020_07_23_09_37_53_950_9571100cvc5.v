Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test65.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_verit/x2020_07_23_09_37_53_950_9571100cvc5.v". Abort.
  Verit_Checker "x2020_07_23_09_37_53_950_9571100.smt_in" "x2020_07_23_09_37_53_950_9571100.cvc5oldpf".
End test65.

