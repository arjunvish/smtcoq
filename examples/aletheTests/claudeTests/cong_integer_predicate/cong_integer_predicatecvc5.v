(* Demonstrates the get_args_isfrms fix for congruence over an integer inequality predicate
   (<, <=, >, >=). Step t8 derives "(>= n m) = (>= n m)" via `cong` from two premises proving
   n=n and m=m - the same shape as real sledgehammer-benchmarks failures (e.g.
   examples/regress/sledgehammer-benchmarks/isabelle-mirabelle/HOL-Library/smt_cvc4/
   x2020_07_23_16_01_56_200_5114158.cvc5oldpf's step t8: "(>= (+ n_d (* -1 n_d)) ...) =
   (>= 0 -1)"). process_cong dispatches this to cong_find_implicit_args (to work out the
   congruence's "implicit" argument-position equalities), which calls get_args_isfrms on the
   conclusion's LHS to find its arguments.

   Before the fix, get_args_isfrms's match arm for Lt/Leq/Gt/Geq just gave up immediately:
   `raise (Debug "congruence over integer predicates unsupported")`, unlike the
   And/Or/Imp/Xor/Eq/Ite/App cases just above/below it, which all know how to list their own
   arguments. Fix: list [x; y] the same way the Eq arm does. This is sound even though
   inequalities aren't symmetric like `=` is, because nothing downstream treats the outer
   relation as symmetric on account of it coming from get_args_isfrms: cong_find_implicit_args's
   own symmetry-aware argument reversal is pattern-guarded to Eq(_,_) specifically (so it never
   fires here), and the actual derivation - EqcpAST, `x=a -> y=b -> P(x,y) -> P(a,b)` - is a
   generic substitutivity axiom that holds for any predicate P, symmetric or not.

   This fix alone doesn't make all 3 examples/regress files that failed on this exact
   limitation pass (see CLAUDE.md for the current state): one still errors on a different,
   unrelated bug once this one is out of the way, and the other two now get past preprocessing
   but both fail the same way at a later, unrelated step ("BuildDef2", nothing to do with
   congruence) - previously masked entirely by the crash this fix removes. *)

Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.

Section CongIntegerPredicate.
  Verit_Checker "cong_integer_predicate.smt2" "cong_integer_predicate.cvc5pf".
End CongIntegerPredicate.
