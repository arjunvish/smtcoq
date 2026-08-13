(* Demonstrates the veritParser.mly fix: cvc5 sometimes emits n-ary (3+ argument) +/-/*, e.g.
   "(+ x x x)", but the parser only accepted the strictly-binary SMT-LIB core form (2 args),
   since Plus/Minus/Mult are binary constructors used throughout veritAst.ml. The fix left-folds
   any extra arguments into nested binary applications at parse time. Steps t1/t2/t3 are
   self-contained, otherwise-unused facts ("(+ x x x) = (+ x x x)", etc.) included purely to
   exercise parsing a 3-arg +/-/*; before the fix, any one of them would make the whole file
   fail to parse with a VeritParser.Error, even though none of them are needed to derive the
   empty clause. The actual refutation (a0/t0/t4) doesn't involve arithmetic at all, to isolate
   the parser issue from unrelated LIA machinery. *)

Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.

Section ParserNaryArith.
  Verit_Checker "parser_nary_arith.smt2" "parser_nary_arith.cvc5pf".
End ParserNaryArith.
