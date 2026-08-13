(* Demonstrates the veritLexer.mll fix: a bare negative numeral like "-1" (no surrounding
   parens, as opposed to the SMT-LIB "(- 1)" application form) used to lex as SYMBOL "-1"
   instead of INT (-1), because "-1" matches both the `int` and `symbol` lexer rules with the
   same length and `symbol` was listed first (ocamllex breaks length ties by rule order). Step
   t1 below is a self-contained, otherwise-unused fact ("-1 = -1") included purely to exercise
   parsing/lexing a bare "-1" term; it used to fail with "SmtMaps.get_fun: function symbol
   \"-1\" not found" since "-1" isn't a declared function. The actual refutation (a0/t0/t2)
   doesn't involve arithmetic at all, to isolate the lexer issue from unrelated LIA machinery. *)

Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.

Section LexerNegativeInt.
  Verit_Checker "lexer_negative_int.smt2" "lexer_negative_int.cvc5pf".
End LexerNegativeInt.
