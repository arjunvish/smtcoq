Require Import SMTCoq.SMTCoq.
Require Import Bool.
Section Testboolsimp1Debug.
  Verit_Checker
    "../smt/boolsimpsanity.smt2"
    "../proof/boolsimpsanity.pf".
End Testboolsimp1Debug.
