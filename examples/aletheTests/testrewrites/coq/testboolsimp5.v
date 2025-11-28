Require Import SMTCoq.SMTCoq.
Require Import Bool.
Section Testboolsimp5Debug.
  Verit_Checker
    "../smt/boolsimp5.smt2"
    "../proof/boolsimp5.pf".
End Testboolsimp5Debug.
