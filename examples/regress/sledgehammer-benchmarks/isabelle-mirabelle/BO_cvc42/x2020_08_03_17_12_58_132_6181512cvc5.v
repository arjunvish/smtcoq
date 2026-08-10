Add Rec LoadPath "../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test11.
  Goal True. idtac "". idtac "isabelle-mirabelle/BO_cvc42/x2020_08_03_17_12_58_132_6181512cvc5.v". Abort.
  Verit_Checker "x2020_08_03_17_12_58_132_6181512.smt_in" "x2020_08_03_17_12_58_132_6181512.cvc5oldpf".
End test11.

