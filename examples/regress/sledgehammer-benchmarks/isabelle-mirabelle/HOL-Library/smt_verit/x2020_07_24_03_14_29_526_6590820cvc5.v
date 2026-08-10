Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test44.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_verit/x2020_07_24_03_14_29_526_6590820cvc5.v". Abort.
  Verit_Checker "x2020_07_24_03_14_29_526_6590820.smt_in" "x2020_07_24_03_14_29_526_6590820.cvc5oldpf".
End test44.

