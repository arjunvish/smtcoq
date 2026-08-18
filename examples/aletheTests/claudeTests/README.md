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

## Session 3 (`examples/aletheTests/QFUFTests`-fixing session) fixes

See CLAUDE.md's "Session 3" for the full writeups. One fix has a dedicated minimal reproduction,
kept under `examples/aletheTests/QFUFTests/findi/min/` (not copied here) since it's part of that
session's own worked-examples convention (one per `otherSummary.md` category folder):

- `process_cong`'s `and`/`or`-congruence handlers: reversed-premise orientation (`and_cong_prem_fact`
  and the `per_pos1`/`per_pos2` orientation checks) - `examples/aletheTests/QFUFTests/findi/min/min.v`,
  confirmed to fail with `findi: element not found` before the fix and pass (`= true`) after.

The `process_trivial` fixes (`taut_protected`, the `weakened_ids` cross-elimination scoping bug,
the "recursive trivial clause" branch's dangling-reference bug, its non-tail-recursion, and its
`STerm`-blind triviality checks) don't have dedicated examples here, for the same reason as the
`extend_cl_aux`/`process_subproof_aux` sites above: each needs a specific multi-step certificate
shape (an axiom fact already folded into a single-premise alias by an earlier pass, feeding a
`tautology` step; a step depending on two independently-trivial clauses in turn; or two separately
-`:named` subterms that only turn out to be the same formula once fully dereferenced) that wasn't
practical to hand-derive standalone in the time available. Verified instead via the real
`examples/aletheTests/QFUFTests/get_clause/01`, `/02`, `get_eq/02`, `trans/02`, and `findi/01`
benchmarks (each confirmed to crash - or, for `findi/01`, return `false` - before its respective
fix, and pass afterward) - see CLAUDE.md for the full diagnosis and the specific failure each one
produces. The `process_cong` duplicate-disjunct fix (`first_occurrence_mask`) likewise has no
dedicated example - constructing a minimal `Or`-congruence with a genuine duplicate disjunct that
isn't also saved by some other simplification turned out to need real-proof structure - verified
instead via `findi/01` and `/02` directly, both now `= true`.
