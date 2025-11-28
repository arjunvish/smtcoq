Require Import SMTCoq.SMTCoq.
Require Import Bool.
Section Testboolsimp1Debug.
  Verit_Checker
    "../smt/boolsimp1.smt2"
    "../proof/boolsimp1.pf".
End Testboolsimp1Debug.
