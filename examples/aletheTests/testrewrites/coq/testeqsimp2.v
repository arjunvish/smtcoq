Require Import SMTCoq.SMTCoq.
Require Import Bool.
Section Testeqsimp2Debug.
  Verit_Checker
    "../smt/eqsimp2.smt2"
    "../proof/eqsimp2.pf".
End Testeqsimp2Debug.
