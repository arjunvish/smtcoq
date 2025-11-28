Require Import SMTCoq.SMTCoq.
Require Import Bool.
Section Testorsimp4Debug.
  Verit_Checker
    "../smt/orsimp4.smt2"
    "../proof/orsimp4.pf".
End Testorsimp4Debug.
