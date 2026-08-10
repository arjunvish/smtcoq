Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test56.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_verit/x2020_07_23_08_55_10_288_8633312cvc5.v". Abort.
  Verit_Checker "x2020_07_23_08_55_10_288_8633312.smt_in" "x2020_07_23_08_55_10_288_8633312.cvc5oldpf".
End test56.

