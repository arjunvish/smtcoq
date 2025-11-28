Require Import SMTCoq.SMTCoq.
Require Import Bool.
Section Testboolsimp6Debug.
  Verit_Checker
    "../smt/boolsimp6.smt2"
    "../proof/boolsimp6.pf".
End Testboolsimp6Debug.
