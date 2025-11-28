Require Import SMTCoq.SMTCoq.
Require Import Bool.
Section Testboolsimp2Debug.
  Verit_Checker
    "../smt/boolsimp2.smt2"
    "../proof/boolsimp2.pf".
End Testboolsimp2Debug.
