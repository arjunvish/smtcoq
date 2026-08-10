Add Rec LoadPath "../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test14.
  Goal True. idtac "". idtac "isabelle-mirabelle/BO_cvc42/x2020_08_03_15_24_49_644_6536112cvc5.v". Abort.
  Verit_Checker "x2020_08_03_15_24_49_644_6536112.smt_in" "x2020_08_03_15_24_49_644_6536112.cvc5oldpf".
End test14.

