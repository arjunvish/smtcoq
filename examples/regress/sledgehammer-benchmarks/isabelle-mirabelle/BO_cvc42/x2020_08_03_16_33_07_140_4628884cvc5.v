Add Rec LoadPath "../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test22.
  Goal True. idtac "". idtac "isabelle-mirabelle/BO_cvc42/x2020_08_03_16_33_07_140_4628884cvc5.v". Abort.
  Verit_Checker "x2020_08_03_16_33_07_140_4628884.smt_in" "x2020_08_03_16_33_07_140_4628884.cvc5oldpf".
End test22.

