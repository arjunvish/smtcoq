(* Demonstrates the process_trivial "pids" fix (a minimized, renamed version of a real
   sledgehammer-benchmarks failure - see CLAUDE.md for the full trace). The proof derives
   (g \/ u=s) and its negation from a0/a1 via t0/t1, then separately re-derives
   ~(g \/ s=u) - the *symmetric* form - from a0 via a "not"-congruence chain (t2..t7) that
   goes through SMTCoq's atom interning, which canonicalizes the direction of a bare
   equality (u=s and s=u intern to the same atom), making the clause {~g, s=u} - built while
   eliminating a redundant intermediate step in that chain - trivially true and eligible for
   elimination by process_trivial. Before the fix, eliminating it incorrectly carried forward
   an extra, by-then-redundant premise into the replacement resolution step, which finds no
   literal left to cancel against and collapses to the checker's C._true sentinel - so the
   certificate stops concluding the empty clause, even though every individual step still
   checks out locally (Verit_Checker_Debug reports no step failure). *)

Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.

Section TrivialUnsoundPremise.
  Verit_Checker "trivial_unsound_premise.smt2" "trivial_unsound_premise.cvc5pf".
End TrivialUnsoundPremise.
