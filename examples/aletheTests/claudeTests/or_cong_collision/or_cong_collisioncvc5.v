(* Demonstrates the process_cong Or-congruence premise-interleaving fix.

   The proof derives `Eq(Or xs, Or ys)` for a 3-arg Or where substituting `y=(f x)` into the
   `y=(f x)` disjunct produces `(f x)=(f x)` (via `eq_simplify`+`not_simplify`+`or_simplify`
   collapsing it away) while another, untouched disjunct is `Not(g (f x))` and a third,
   substituted disjunct becomes `g (f x)` positively - i.e. the *substituted* value of one
   disjunct happens to coincide (up to negation) with the *unchanged* value of a different,
   unrelated disjunct.

   Before the fix, `process_cong`'s Or-congruence builder resolved all `eqp2`
   (substitution) facts as one group, then all `orn` (projection) facts as a second group,
   rather than interleaving them position by position. Folding the "unrelated" disjunct's
   `orn`-based projection premise into the accumulated clause introduces `g (f x)` positively
   at the same time the still-unprocessed `Not(g (f x))` (from the untouched disjunct) is still
   sitting in the accumulator - two simultaneous complementary literal pairs in one two-clause
   fold. SmtCoq's checker-side `C.resolve` (State.v) is a sorted merge that finds and cancels
   only the first complementary pair it encounters per pairwise fold, silently leaving the
   second, unrelated pair's literals stuck in the result. That residue never gets cancelled by
   anything downstream, and the final derivation collapses to the checker's `_true` give-up
   sentinel instead of the empty clause - checked cleanly (no step individually flagged as
   invalid, since a `_true` weakening is still locally sound) but returning `false` overall.

   Fix: build the Or-congruence's premise list by interleaving, one disjunct position at a
   time, its (optional) `eqp2`/`eqp1` substitution fact immediately followed by its own `orn`
   projection fact, instead of grouping all substitutions before all projections. Each
   position's temporaries are then fully consumed (folded into `Or ys`/`Or xs`) before a later
   position can introduce a colliding value, so no fold step is ever handed more than one
   complementary pair at once.

   Verified: this is exactly `examples/aletheTests/sanitychecktests/test6cvc5.v`'s proof
   (copied here as a standalone worked example) - confirmed to return `false` before this fix
   and `true` after it, with the checker computing a residual, non-empty `[_true; _true]`
   final clause (found via a purpose-built `Verit_Checker_Trace` diagnostic) instead of the
   empty clause pre-fix. `examples/aletheTests/sanitychecktests/test7verit.v` hit the same
   underlying bug independently and is fixed by the same change. *)

Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.

Section OrCongCollision.
  Verit_Checker "or_cong_collision.smt2" "or_cong_collision.cvc5pf".
End OrCongCollision.
