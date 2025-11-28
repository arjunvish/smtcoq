Require Import SMTCoq.SMTCoq.
Require Import Bool.
Section Testnotsimp1Debug.
  Verit_Checker
    "../smt/notsimp1.smt2"
    "../proof/notsimp1.pf".
End Testnotsimp1Debug.
