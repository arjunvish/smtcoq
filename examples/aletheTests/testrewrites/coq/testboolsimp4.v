Require Import SMTCoq.SMTCoq.
Require Import Bool.
Section Testboolsimp4Debug.
  Verit_Checker
    "../smt/boolsimp4.smt2"
    "../proof/boolsimp4.pf".
End Testboolsimp4Debug.
