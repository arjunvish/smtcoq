Add Rec LoadPath "../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test20.
  Goal True. idtac "". idtac "isabelle-mirabelle/BO_cvc42/x2020_08_03_15_23_49_010_6452792cvc5.v". Abort.
  Verit_Checker "x2020_08_03_15_23_49_010_6452792.smt_in" "x2020_08_03_15_23_49_010_6452792.cvc5oldpf".
End test20.

