Require Import SMTCoq.SMTCoq.
Require Import Bool.
Section Testboolsimp7Debug.
  Verit_Checker
    "../smt/boolsimp7.smt2"
    "../proof/boolsimp7.pf".
End Testboolsimp7Debug.
