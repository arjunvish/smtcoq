Require Import SMTCoq.SMTCoq.
Require Import Bool.
Section Testeqsimp1Debug.
  Verit_Checker
    "../smt/eqsimp1.smt2"
    "../proof/eqsimp1.pf".
End Testeqsimp1Debug.
