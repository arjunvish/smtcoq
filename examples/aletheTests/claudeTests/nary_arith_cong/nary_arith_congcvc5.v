(* Demonstrates the cong_find_implicit_args fix for a `cong` step over an n-ary `+`/`-`/`*`
   with more than 2 explicit premises (one per flat argument, matching real cvc5 output - e.g.
   `(+ a b c) = (+ a' b' c')` derived from 3 premises `a=a'`, `b=b'`, `c=c'`).

   `Plus`/`Minus`/`Mult` are strictly binary constructors here (veritParser.mly left-folds n-ary
   +/-/* into nested binary applications at parse time - see CLAUDE.md's veritParser.mly section),
   so `get_args_isfrms` only ever reports 2 arguments for such a node, however many premises
   cvc5 actually gave it. `cong_find_implicit_args`'s normal matching (position-by-position,
   at most one explicit premise per position, with unmatched positions treated as implicit
   reflexivity) has no way to consume 3+ premises against a 2-argument node, and gave up with
   "can't find implicit premise to congr".

   t1's own conclusion is written with cvc5's flat ternary `(+ a b c)` (parsing, via the earlier
   n-ary left-fold fix, to the identical `Plus(Plus(a,b),c)` shape as the smt2 file's explicitly
   double-nested `(+ (+ a b) c)` - the smt2-root parser, unlike the proof-file parser, only
   supports binary +/-/*, so the assertions here use explicit nesting to stay within that,
   independent, pre-existing limitation while still exercising the exact same internal shape).

   Fix: `fold_nary_arith_prem` recursively folds the extra premises pairwise - inserting one
   synthetic `EqcoAST`+`ResoAST` congruence step per fold, exactly mirroring the shape
   `process_cong`'s own "no implicit equalities" case already builds for a genuine 2-ary node -
   down to exactly 2 combined premises matching `Plus`/`Minus`/`Mult`'s own 2-argument structure,
   which the existing (already-correct, already-tested) binary-congruence code then handles
   unchanged. *)

Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.

Section NaryArithCong.
  Verit_Checker "nary_arith_cong.smt2" "nary_arith_cong.cvc5pf".
End NaryArithCong.
