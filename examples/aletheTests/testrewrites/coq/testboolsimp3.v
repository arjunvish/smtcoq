Require Import SMTCoq.SMTCoq.
Require Import Bool.
Section Testboolsimp3Debug.
  Verit_Checker
    "../smt/boolsimp3.smt2"
    "../proof/boolsimp3.pf".
End Testboolsimp3Debug.
