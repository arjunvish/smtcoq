Add Rec LoadPath "../../../src" as SMTCoq.

Require Import SMTCoq.SMTCoq.
Require Import Bool.
   
Require Import ZArith.
Require Import Int31.
   
Section Test.
  Verit_Checker "testtaut.smt2" "testtaut.pf".
End Test.