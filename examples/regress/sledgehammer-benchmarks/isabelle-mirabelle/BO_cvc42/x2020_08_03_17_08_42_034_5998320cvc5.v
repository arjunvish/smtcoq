Add Rec LoadPath "../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test23.
  Goal True. idtac "". idtac "isabelle-mirabelle/BO_cvc42/x2020_08_03_17_08_42_034_5998320cvc5.v". Abort.
  Verit_Checker "x2020_08_03_17_08_42_034_5998320.smt_in" "x2020_08_03_17_08_42_034_5998320.cvc5oldpf".
End test23.

