(* Demonstrates the hoist_nested_subproofs fix. This is a minimized, renamed version of a real
   sledgehammer-benchmarks failure (see CLAUDE.md for the full trace and root-cause writeup).
   The key structural feature: the subproof "t7" (anchor .. discharge, t7.a0/t7.a1 .. t7) has,
   *inside its own body*, two separate "equiv_simplify" steps (t7.t0 and t7.t4). Each
   equiv_simplify gets elaborated by process_simplify into its own synthetic subproof (via
   simplify_to_subproof) - so by the time process_subproof runs, t7's body itself contains
   more SubproofAST nodes, i.e. a subproof nested inside a subproof.
   process_subproof_aux recovers a subproof's hypotheses as proven facts by resolving against
   whatever remains of the certificate *after* it - which must be the true final derivation for
   that recovery to compute down to exactly what's needed. That holds for t7 itself (real
   top-level subproof), but not for the two synthetic subproofs nested inside t7's body: for
   them, "the rest of the certificate" was only the sibling steps within t7, whose last step is
   just some unrelated intermediate derivation - so the recovery leaves genuine leftover
   literals in the result, and the certificate stops concluding the empty clause even though
   every individual Res/Weaken step it goes through remains locally valid. *)

Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.

Section NestedSubproof.
  Verit_Checker "nested_subproof.smt2" "nested_subproof.cvc5pf".
End NestedSubproof.
