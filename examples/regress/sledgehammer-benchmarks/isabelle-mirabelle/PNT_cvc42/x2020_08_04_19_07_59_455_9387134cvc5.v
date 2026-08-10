Add Rec LoadPath "../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test92.
  Goal True. idtac "". idtac "isabelle-mirabelle/PNT_cvc42/x2020_08_04_19_07_59_455_9387134cvc5.v". Abort.
  Verit_Checker "x2020_08_04_19_07_59_455_9387134.smt_in" "x2020_08_04_19_07_59_455_9387134.cvc5oldpf".
End test92.

