(* Demonstrates the code shape targeted by the get_expr/STerm fix in process_cong's
   equality-of-equalities case (Eq (Eq (x,y), Eq (a,b))). Step t0's conclusion
   "(= (= p q) (= r s))" is tagged ":named @eqeq" - store_shared_terms rewrites *every*
   occurrence of a :named formula (including its own defining one) into an STerm reference, so
   by the time process_cong examines t0's clause, the literal is `STerm "@eqeq"`, confirmed via
   direct instrumentation, not a literal `Eq (Eq _, Eq _)`. Without dereferencing through
   get_expr first, the specialized "equality-of-equalities" branch (which produces a direct,
   short proof via Equn1/Equn2) misses this shape entirely and falls through to a generic
   "predicate congruence" fallback (EqcpAST) - which happens to compute its own get_expr
   independently and still succeeds *for this specific example* (just via a longer, less
   direct proof), so this file alone doesn't cleanly reproduce a pre-fix crash. The real
   sledgehammer-benchmarks failures this fix was found from involved additional structure
   (nested congruence, iff- vs term-typing checks upstream of the fallback) where that generic
   path did not save it; see CLAUDE.md for the general description. This file is kept as a
   minimal illustration of the code shape - the STerm literal reaching process_cong - rather
   than a verified before/after crash reproduction. *)

Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.

Section STermCong.
  Verit_Checker "sterm_cong.smt2" "sterm_cong.cvc5pf".
End STermCong.
