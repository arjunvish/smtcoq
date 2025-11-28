Require Import SMTCoq.SMTCoq.
Require Import Bool.
Section Testeqsimp11Debug.
  Verit_Checker
    "../smt/eqsimp11.smt2"
    "../proof/eqsimp11.pf".
End Testeqsimp11Debug.
