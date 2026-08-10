Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test64.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_verit/x2020_07_23_14_32_00_883_17987914cvc5.v". Abort.
  Verit_Checker "x2020_07_23_14_32_00_883_17987914.smt_in" "x2020_07_23_14_32_00_883_17987914.cvc5oldpf".
End test64.

