Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test60.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_verit/x2020_07_23_08_55_07_259_8627852cvc5.v". Abort.
  Verit_Checker "x2020_07_23_08_55_07_259_8627852.smt_in" "x2020_07_23_08_55_07_259_8627852.cvc5oldpf".
End test60.

