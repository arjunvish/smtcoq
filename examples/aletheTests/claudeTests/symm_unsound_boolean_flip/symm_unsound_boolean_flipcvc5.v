(* Demonstrates process_same's unsound elimination of `symm` for a Boolean/`iff`-typed
   equality (as opposed to a genuine first-order term equality, whose direction SMTCoq's atom
   interning canonicalizes via Atom.mk_eq_sym - see CLAUDE.md's "process_same" section for the
   full argument). This is a minimized version of a real sledgehammer-benchmarks failure shape
   (isabelle-mirabelle/HOL-Library's x2020_07_23_16_..._5114158 and x2020_07_23_15_..._5083584):
   `p` stands in for an arithmetic atom (e.g. `(>= n_d 1)`), `r` for a related one (e.g.
   `(< n_d 1)`) satisfying `r <-> not p`.

   a1 asserts `(= r (not p))`; t18 flips it via `symm` to `(= (not p) r)` - the direction t16
   (a fixed `equiv_pos2` axiom instance) needs to resolve against `a0: (not p)` and derive `r`.

   Before the fix, `process_same` eliminated every `symm` step unconditionally, aliasing t18's
   id straight to a1's - so t28's premises silently became (t16 a1 a0) instead of (t16 t18 a0).
   Since `(= (not p) r)` and `(= r (not p))` are distinct, order-sensitive `Fiff` literals for a
   Boolean equality (unlike a term equality, which SMTCoq's interning would canonicalize to the
   same atom either way), t16 and a1 no longer share a cancelable pivot, and the certificate
   silently stops concluding the empty clause - with no individual step ever reported as failing
   by Verit_Checker_Debug, since Res steps are unconditionally valid regardless of which pivot
   (if any) they find. The fix builds an explicit, checker-verified derivation of the flipped
   clause instead of aliasing ids whenever the equality isn't direction-canonicalized. *)

Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.

Section SymmUnsoundBooleanFlip.
  Verit_Checker "symm_unsound_boolean_flip.smt2" "symm_unsound_boolean_flip.cvc5pf".
End SymmUnsoundBooleanFlip.
