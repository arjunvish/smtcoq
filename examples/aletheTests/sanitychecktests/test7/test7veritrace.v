Add Rec LoadPath "../../../../src" as SMTCoq.

Require Import SMTCoq.SMTCoq.
Require Import Bool.

Require Import ZArith.
Require Import Int31.

Local Open Scope int31_scope.

Section Test7Trace.
     Verit_Checker_Trace "test7.smt2" "test7verit.pf".
End Test7Trace.
