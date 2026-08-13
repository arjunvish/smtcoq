# Folder Description

Minimal, hand-written (or generated) representative examples for each issue described in
`CLAUDE.md` at the repo root. Each subfolder is a self-contained `.smt2` + `.cvc5pf` + `.v`
triple (following the same convention as `../sanitychecktests`), runnable directly with
`coqc <name>cvc5.v` from inside the subfolder, or all together via `examples/regress`'s harness
if added there. All of them currently check `= true` against the fixed code in this branch; see
each `.v` file's header comment and CLAUDE.md for what specifically they demonstrate and, where
verified, what used to go wrong before the corresponding fix.

| Folder                     | Demonstrates                                                                | Verified before/after? |
|-----------------------------|------------------------------------------------------------------------------|-------------------------|
| `lexer_negative_int`        | veritLexer.mll: bare `-1` lexing as SYMBOL instead of INT                    | yes |
| `parser_nary_arith`         | veritParser.mly: n-ary (3+ arg) `+`/`-`/`*` not parsing                      | yes |
| `sterm_cong`                | get_expr/STerm dereferencing in process_cong's `Eq(Eq,Eq)` case              | code shape only - see file header |
| `trivial_unsound_premise`   | process_trivial's `pids` unsoundness (checker returns `false`)               | yes |
| `nested_subproof`           | process_subproof: subproof nested inside another subproof's body             | yes |
| `stack_overflow_cong`       | process_cong non-tail-recursion (+ several other passes found the same way)  | yes |
| `stack_overflow_trans`      | process_trans non-tail-recursion                                             | yes |
| `cong_integer_predicate`    | `get_args_isfrms`: congruence over `</<=/>/>=` unsupported                   | yes |
| `symm_unsound_boolean_flip` | `process_same`: unsound unconditional elimination of `symm` for Boolean equalities | yes |
| `nary_arith_cong`           | `cong_find_implicit_args`: `cong` over n-ary `+`/`-`/`*` with 3+ premises unsupported | yes |
| `or_cong_collision`         | `process_cong`'s `Or`-congruence: grouped (not interleaved) premise fold order lets an accidental cross-disjunct literal collision defeat `C.resolve`'s single-pivot merge | yes |
| `eqcongruentpred_polarity`  | `mkCongrPred`: `concl`/`prem_P` picked by fixed position instead of polarity, mismatched for a non-symmetric predicate (`<=`) | yes |

`cong_integer_predicate`'s fix, by itself, did not make all 3 of the `examples/regress` files
that hit this exact limitation pass - see CLAUDE.md's writeup: one used to still error on an
unrelated bug (fixed by `nary_arith_cong`'s fix), and the other two got past preprocessing but
returned `false` at an unrelated later step (`process_same`'s `BuildDef2` bug, previously masked
entirely by this crash) - since fixed by `symm_unsound_boolean_flip`'s fix, so both now pass.
`examples/regress` is 433/433 as of `nary_arith_cong`'s fix.

`stack_overflow_cong` and `stack_overflow_trans` include the `generate.py` script used to
produce their (long, repetitive) `.cvc5pf` file, since hand-writing thousands of steps isn't
practical - regenerate with a larger N if the included one happens not to be long enough to
overflow the stack on your system (see the comment in each `.v` file).

Two sites sharing the exact same get_expr/STerm fix as `sterm_cong` - `extend_cl_aux` and
`process_subproof_aux`'s hypothesis dereferencing - don't have their own dedicated example
here: constructing a minimal proof that cleanly fails without the fix (rather than being saved
by some other, unrelated get_expr call elsewhere in the same code path) turned out to need more
of the surrounding real-proof structure than was practical to hand-derive reliably in the time
available. See CLAUDE.md's "get_expr/STerm dereferencing fixes" section for the textual
description of all three sites.

A further fix from the `sanitychecktests`-fixing session (see CLAUDE.md's "Session 2") likewise
doesn't have a dedicated example here: `extend_cl_aux`'s `Ite1AST` branch-index fix (needs an
actual eliminated-subproof scenario combined with a `:rule ite1`-tagged consumer, i.e. real
subproof-elimination machinery, not just a shape that can be hand-assembled standalone).
Verified via `examples/aletheTests/sanitychecktests/test7verit.v` - see CLAUDE.md for the full
diagnosis.

The same session's `VeritSyntax.mk_clause` `Reso`/`ThReso` premise-reordering fix (see CLAUDE.md's
own section on it) doesn't have one either, for a different reason: it's a sound, defensive fix
that turned out - on later, careful re-verification - to be a no-op for every test in either
suite, so there's no failing case to demonstrate a before/after with.
