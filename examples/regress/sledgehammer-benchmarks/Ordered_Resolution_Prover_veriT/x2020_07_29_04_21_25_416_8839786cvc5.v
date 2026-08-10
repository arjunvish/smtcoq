Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test137.
  Goal True. idtac "". idtac "Ordered_Resolution_Prover_veriT/x2020_07_29_04_21_25_416_8839786cvc5.v". Abort.
  Verit_Checker "x2020_07_29_04_21_25_416_8839786.smt_in" "x2020_07_29_04_21_25_416_8839786.cvc5oldpf".
End test137.

