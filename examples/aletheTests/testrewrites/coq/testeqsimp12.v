Require Import SMTCoq.SMTCoq.
Require Import Bool.
Section Testeqsimp12Debug.
  Verit_Checker
    "../smt/eqsimp12.smt2"
    "../proof/eqsimp12.pf".
End Testeqsimp12Debug.
