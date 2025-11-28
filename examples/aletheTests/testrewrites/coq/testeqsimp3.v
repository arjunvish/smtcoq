Require Import SMTCoq.SMTCoq.
Require Import Bool.
Section Testeqsimp3Debug.
  Verit_Checker
    "../smt/eqsimp3.smt2"
    "../proof/eqsimp3.pf".
End Testeqsimp3Debug.
