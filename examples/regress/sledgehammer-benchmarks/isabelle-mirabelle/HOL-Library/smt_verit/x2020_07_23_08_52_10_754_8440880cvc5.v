Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test49.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_verit/x2020_07_23_08_52_10_754_8440880cvc5.v". Abort.
  Verit_Checker "x2020_07_23_08_52_10_754_8440880.smt_in" "x2020_07_23_08_52_10_754_8440880.cvc5oldpf".
End test49.

