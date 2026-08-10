Add Rec LoadPath "../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test28.
  Goal True. idtac "". idtac "isabelle-mirabelle/BO_cvc42/x2020_08_03_16_51_48_838_5354134cvc5.v". Abort.
  Verit_Checker "x2020_08_03_16_51_48_838_5354134.smt_in" "x2020_08_03_16_51_48_838_5354134.cvc5oldpf".
End test28.

