(* Demonstrates the pre-existing, unfixed `cong_find_implicit_args`/`get_args_isfrms`
   limitation: congruence over an integer inequality predicate (<, <=, >, >=) is not supported.
   Step t8 derives "(>= n m) = (>= n m)" via `cong` from two premises proving n=n and m=m -
   the same shape as real sledgehammer-benchmarks failures (e.g.
   examples/regress/sledgehammer-benchmarks/isabelle-mirabelle/HOL-Library/smt_cvc4/
   x2020_07_23_16_01_56_200_5114158.cvc5oldpf's step t8: "(>= (+ n_d (* -1 n_d)) ...) =
   (>= 0 -1)"). process_cong dispatches this to cong_find_implicit_args (to work out the
   congruence's "implicit" argument-position equalities), which calls get_args_isfrms on the
   conclusion's LHS to find its arguments - but get_args_isfrms's match arm for
   Lt/Leq/Gt/Geq (src/verit/veritAst.ml, in cong_find_implicit_args's vicinity) just gives up
   immediately: `raise (Debug "congruence over integer predicates unsupported")`, unlike the
   And/Or/Imp/Xor/Eq/Ite/App cases just above/below it, which all know how to list their own
   arguments. This is NOT fixed by anything in CLAUDE.md - it's a separate, deeper, pre-existing
   limitation affecting 3 files in examples/regress (all failing with this exact message, or the
   closely related "can't find implicit premise to congr" once this raise is reached from a
   slightly different call path). A real fix would need get_args_isfrms to handle Lt/Leq/Gt/Geq
   the same way it already handles Eq (list [x; y] as the two implicit-argument positions). *)

Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.

Section CongIntegerPredicate.
  Verit_Checker "cong_integer_predicate.smt2" "cong_integer_predicate.cvc5pf".
End CongIntegerPredicate.
