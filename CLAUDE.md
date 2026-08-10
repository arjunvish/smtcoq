# Session summary: Alethe/veriT/cvc5 preprocessing fixes

This document summarizes uncommitted work on `src/verit/veritAst.ml`,
`src/verit/veritLexer.mll`, `src/verit/veritParser.mly`, and `examples/Makefile`, plus the new
`examples/regress/` regression suite. It's meant for review before committing, and as a record
of what was found and why each change was made.

**Net result:** the `examples/regress` suite (433 `.v` files: 5 small hand-picked tests +
`sledgehammer-benchmarks`, a large corpus of real cvc5/veriT proofs from Isabelle's Sledgehammer)
went from a state where a large fraction of the sledgehammer benchmarks either crashed outright
or produced a checked-but-wrong `= false`, to **429/433 passing**, with 1 known-unresolved
`false` and 3 known-unresolved errors (both described at the bottom, with what was ruled out).

Run it yourself with `cd examples && make test` (see "Build/test infra" below).

**Worked examples:** `examples/aletheTests/claudeTests/` has a minimal, standalone
`.smt2`/`.cvc5pf`/`.v` triple for each issue described below (see `README.md` there for the
full list) — each one is linked from the relevant section here.

## The bug-fixing arc: errors → stack overflows → wrong answers → mostly fixed

Working through the `sledgehammer-benchmarks` corpus (real-world proofs) surfaced problems in
layers, where fixing one exposed the next:

1. **Errors.** Some proofs crashed outright during OCaml preprocessing with `Debug` exceptions
   like "expecting head of clause to be either an equality or an iff" — even though the clause
   *was* one. Cause: a formula introduced earlier via an SMT-LIB `:named` tag gets rewritten to a
   `STerm` (shared-term reference) at its later occurrences; several pattern matches on term
   shape weren't dereferencing through `STerm` first, so they fell through to "unexpected shape"
   error paths. Fixed in `process_cong`, `extend_cl_aux`, and `process_subproof_aux` (see
   "get_expr/STerm dereferencing fixes" below). Worked example:
   [`sterm_cong`](examples/aletheTests/claudeTests/sterm_cong).

2. **Stack overflows.** Once those crashes were fixed, larger proofs made it further into
   preprocessing but then hit OCaml's `Stack_overflow`. Cause: `process_cong`, `process_trans`,
   `process_simplify`, `process_subproof`, `process_trivial`, and a number of helper/earlier-pass
   functions (`store_shared_terms`, `process_fins`, `process_hole`, `process_proj`,
   `process_notnot`, `replace_prem`/`process_same`, `extend_cl`) were all written as
   non-tail-recursive recursion — typically `step_result @ recurse tl` or `x :: recurse tl` —
   which builds one native stack frame per certificate step before any of it can return.
   Real proofs need to be surprisingly long (thousands of steps, not the ~100-line raw proofs
   that happen to make up the current `sledgehammer-benchmarks` corpus in this repo) before this
   actually bites, which is presumably why several of these went unnoticed even after the
   original round of tail-recursion fixes - they were only found by deliberately constructing a
   long enough proof to trigger the crash (see the worked examples below) rather than by
   anything in the existing corpus. Fixed by converting every one of these to proper tail
   recursion via an explicit accumulator (see "Tail-recursion / stack-overflow fixes" below).
   Worked examples: [`stack_overflow_cong`](examples/aletheTests/claudeTests/stack_overflow_cong),
   [`stack_overflow_trans`](examples/aletheTests/claudeTests/stack_overflow_trans).

3. **Wrong answers (`= false`).** Once proofs could run to completion, a lot of them now
   *checked cleanly but returned `false`* — the C-value SMTCoq's proof checker computes when a
   step it verified turns out to be `C._true` (checker's I-couldn't-verify-this sentinel) or the
   final clause isn't actually empty. This is the "it looks like it ran fine but the answer is
   wrong" failure mode, and it's the hardest to debug because nothing crashes or throws — you
   have to trace which step's *computed* clause diverges from its *declared* one. Two distinct,
   unrelated root causes were found and fixed here (see "Correctness fixes" below):
   - an unsound premise being carried forward during recursive trivial-clause elimination
     (`process_trivial`). Worked example:
     [`trivial_unsound_premise`](examples/aletheTests/claudeTests/trivial_unsound_premise).
   - `process_subproof`/`process_subproof_aux`'s "recover hypotheses as facts using the rest of
     the proof" trick being invalid when the subproof it processes is itself nested inside
     another subproof's body. Worked example:
     [`nested_subproof`](examples/aletheTests/claudeTests/nested_subproof).

4. **What's left.** 1 file still returns `false` for a reason not yet found (deep-dived
   extensively, several hypotheses ruled out — see "Known unresolved: Green_cvc42"), and 3 files
   still error out on a pre-existing, unrelated limitation (`cong_find_implicit_args` doesn't
   support congruence over integer predicates) that wasn't touched this session. Worked example
   (unfixed, reproduces the error on purpose):
   [`cong_integer_predicate`](examples/aletheTests/claudeTests/cong_integer_predicate).

---

## Build/test infra

### `examples/Makefile`
Added a `test` target that runs the new regression suite:
```makefile
test:
	bash regress/calltests.sh $(TIMEOUT)
```
`TIMEOUT` defaults to 120 (seconds, per-file) and can be overridden: `make test TIMEOUT=60`.

### `examples/regress/` (new, untracked)
A regression suite: 5 small hand-picked tests (`test1`–`test5`, cvc5 + veriT variants) plus
`sledgehammer-benchmarks/`, a large corpus of real proofs pulled from Isabelle's Sledgehammer
runs against cvc5 and veriT (433 `.v` files total). `calltests.sh` compiles every `.v` file
under it with `coqc` (each in its own directory, since the proof/SMT-LIB file paths inside are
relative), classifies each as `TRUE`/`FALSE`/`ERROR`/`TIMEOUT`, and prints a summary. This is
the harness used to find and verify every fix below — every fix was checked against the full
433-file suite (plus `examples/aletheTests/sanitychecktests`) to confirm zero regressions before
being kept.

Note: `calltests.log` (full per-file output) gets regenerated on every run and is currently
untracked along with the rest of `examples/regress/` — you may want to `.gitignore` it
specifically before committing the suite.

### `examples/aletheTests/claudeTests/` (new, untracked)
The worked examples referenced throughout this document — one `.smt2`/`.cvc5pf`/`.v` triple per
issue, following the same layout as `examples/aletheTests/sanitychecktests`. See that folder's
own `README.md` for the full list and which ones were verified to fail before the corresponding
fix (as opposed to just demonstrating the code shape the fix targets). Each one can be compiled
directly: `cd examples/aletheTests/claudeTests/<name> && coqc <name>cvc5.v`.

---

## `src/verit/veritLexer.mll`

**Bug:** a bare negative numeral like `-1` was lexed as `SYMBOL "-1"` instead of `INT (-1)`,
later failing with `SmtMaps.get_fun: function symbol "-1" not found` since `-1` isn't a declared
function symbol.

**Cause:** `-1` matches both the `int` rule and the `symbol` rule (`-` is a valid leading
character for `simple_symbol`) with the same match length; ocamllex breaks length ties by
favoring whichever rule is listed first, and `symbol` was listed first.

**Fix:** moved the `(int as i)` rule before `symbol`. Positive integers are unaffected (digits
alone can't start a `symbol` match).

Worked example: [`lexer_negative_int`](examples/aletheTests/claudeTests/lexer_negative_int).

## `src/verit/veritParser.mly`

**Bug:** cvc5 sometimes emits n-ary (3+ argument) `+`/`-`/`*`, e.g. `(+ a b c)`, but the parser
only accepted the binary form.

**Cause:** `Plus`/`Minus`/`Mult` are strictly binary constructors used throughout the codebase
(widening them would mean updating every pattern match on `term`).

**Fix:** left-fold any extra arguments into nested binary applications at parse time (sound
since `+`/`-`/`*` are left-associative):
```ocaml
| LPAREN PLUS x=term y=term ys=term* RPAREN
  { List.fold_left (fun acc t -> Plus (acc, t)) (Plus (x, y)) ys }
```
(and similarly for `MINUS`/`MULT`).

Worked example: [`parser_nary_arith`](examples/aletheTests/claudeTests/parser_nary_arith).

---

## `src/verit/veritAst.ml`

### get_expr/STerm dereferencing fixes

**Bug:** a formula introduced earlier via an SMT-LIB `:named` tag gets rewritten (by
`store_shared_terms`) into an `STerm` (shared-term reference) at its *later* occurrences — and
in some cases even at its *defining* occurrence. Several places pattern-matched directly on a
literal's shape (e.g. `Eq (Eq (x,y), Eq (a,b))`, or `Not y`) without dereferencing through
`STerm` first via `get_expr`, so a perfectly valid clause would be missed and fall through to a
generic "unexpected shape" error.

**Fixed in three places**, each now calling `get_expr` before checking shape:
- `process_cong`'s equality-congruence case (`Eq (Eq (x,y), Eq (a,b))` pattern)
- `extend_cl_aux` (premise's head literal)
- `process_subproof_aux` (each hypothesis literal, expected to be `Not y`)

Worked example: [`sterm_cong`](examples/aletheTests/claudeTests/sterm_cong) exercises the
`process_cong` site directly (confirmed via instrumentation that the clause literal really is
an `STerm` at the point `process_cong` examines it) — though note its header comment explains
why this specific file doesn't cleanly reproduce a pre-fix crash (a separate, independent
`get_expr` call in the generic fallback path happens to save this particular example). The other
two sites (`extend_cl_aux`, `process_subproof_aux`) don't have dedicated examples: constructing a
minimal proof that isn't also saved by some other unrelated `get_expr` call elsewhere in the same
code path turned out to need more real-proof structure than was practical to hand-derive
reliably — see `examples/aletheTests/claudeTests/README.md` for more detail.

### Tail-recursion / stack-overflow fixes

Converted from non-tail-recursive (`step @ recurse tl` / `step :: recurse tl`) to tail-recursive
via an explicit accumulator (built up in reverse, `List.rev`/`List.rev_append`'d at the end) in:

- `replace_prem` / `process_same` (used to eliminate `symm` steps)
- `process_cong` — this one's match arms are enormous (each derives a multi-step axiom
  expansion per congruence shape: equality, and, or, imp, xor, ite, not, predicates, uninterpreted
  functions), so every arm needed converting individually
- `process_trans`
- `extend_cl` (walks the remainder of the certificate after a subproof)
- `process_subproof`
- `process_simplify` — same story as `process_cong`: dozens of match arms (one or more per
  `_simplify` rule variant: `and_simplify`, `or_simplify`, `not_simplify`, `implies_simplify`,
  `equiv_simplify`, `bool_simplify`, `connective_def`, `eq_simplify`, `ite_simplify`, ...), every
  one needed converting
- `process_trivial` (see also the correctness fix below, in the same function)
- `store_shared_terms`, `process_fins`, `process_hole`, `process_proj`, `process_notnot` — found
  later, while building the `stack_overflow_cong`/`stack_overflow_trans` worked examples (see
  below): a large synthetic proof, built specifically to overflow the (by-then-already-fixed)
  `process_cong`, instead overflowed near-instantly, before `process_cong` even ran. It turned
  out these five earlier-in-the-pipeline passes (`store_shared_terms` is literally the first pass
  `preprocess_certif` runs) had the exact same non-tail-recursive shape and had never been
  touched by the original round of fixes. Same fix, same pattern, applied here too.

None of these change behavior on small inputs — the whole point is they compute the exact same
result, just without keeping O(number of steps) stack frames alive while doing it. Note that the
`sledgehammer-benchmarks` proofs currently in this repo's `examples/regress` corpus are all quite
short (under ~120 raw lines each) and don't actually exercise any of this — none of these
functions' non-tail-recursion is reachable by anything in the existing regression suite. The
worked examples under `examples/aletheTests/claudeTests/stack_overflow_*` are deliberately
constructed (via a generator script, not hand-written) to be long enough to demonstrate it.

**Also in `process_trivial`, two performance fixes** (needed on top of the tail-recursion fix —
otherwise large proofs would trade a stack overflow for a timeout):
- `get_cl_cog`: a hashtable built once up front, replacing repeated linear scans (`get_cl p cog`)
  over the whole original certificate every time `replace_res` needs a premise's clause.
- Early termination in the nested `process_tl` loop: once every id in `ids` (the fixed set of
  resolution steps using the current trivial clause as a premise) has been found and processed,
  the rest of the certificate is returned untouched instead of being walked to the end for every
  single trivial clause eliminated.

### Correctness fixes (the "checker returns `false`" bugs)

These are the two bugs that actually change *what gets computed*, as opposed to just how it's
computed. Both were found by: picking a file that returns `false` with no `Verit_Checker_Debug`
step-failure reported (or a `Res` step failure that doesn't match any real unsoundness on
inspection), dumping the fully-preprocessed certificate, and manually or semi-automatically
recomputing each `Res`/`Weaken` step's *actual* clause (SMTCoq's checker computes `Res`/`Weaken`
steps fresh from their premises — the "declared" clause in the OCaml-side AST is just a label,
often stale/mislabeled harmlessly, so tracing requires recomputing, not trusting, the declared
value) until the point where the real, checker-computed value diverges from what's needed.

#### 1. `process_trivial`: unsound premise carried through recursive trivial-clause elimination

`process_trivial` eliminates clauses that are "trivial" (contain some literal `x` and its
negation `¬x`, detected modulo double-negation and — since SMTCoq's atom interning
canonicalizes the direction of first-order equalities — modulo equality symmetry too). Each use
of an eliminated clause gets patched: a `Weaken` step re-derives the needed content from an
alternate premise, followed by a `Res` step.

Sometimes eliminating a trivial clause reveals that its *replacement* is *also* trivial (a
recursive cascade). In that case the old code carried forward `pids` — the eliminated clause's
own original co-premises — as extra premises on the final `Res` step of the *next* level of the
cascade, on the theory that they might still be needed.

**The bug:** by the time the cascade reaches that next level, the `Weaken` step already fully
accounts for everything needed (that's what makes it a valid weakening — a superset). The
carried-forward `pids` premise no longer has any literal left to cancel against. SMTCoq's `Res`
checker (`C.resolve` in `State.v`) folds premises pairwise and, if a fold step finds *no*
complementary literal pair, collapses to `C._true` — the checker's "give up" sentinel — right
there. That step still checks out as *valid* (`C._true` is a valid — if useless — weakening of
anything), so nothing crashes; it just means the certificate no longer concludes the empty
clause at the end, and the overall check returns `false` with no specific step ever flagged as
failing.

**Fix:** don't carry `pids` forward in the recursive case — set it to `[]` instead of
`remove t1i p3`.

**Impact:** verified via `Verit_Checker_Debug`, tracing, and full-suite regression checks. Fixed
11 files (mostly the `sledgehammer-benchmarks/isabelle-mirabelle/BO_cvc42` cluster, all sharing
the same cvc5-emitted "Or-congruence over a symmetric equality" proof shape), zero regressions.

#### 2. `process_subproof`: subproofs nested inside subproofs

`process_subproof_aux` turns a `subproof ... discharge` block into flat `Andn`/`Andp`/`Res`
steps by using `pi3` — whatever remains of the *current* certificate scope after the subproof —
as the carrier for recovering the subproof's hypotheses as proven facts. This requires `pi3`'s
last step to be the certificate's *true final derivation* (extended with this subproof's own
residue disjunct) — otherwise the hypothesis-recovery step leaves genuine leftover literals in
its result.

That invariant holds for a subproof written directly in the source proof (its `pi3` really is
the rest of the whole certificate). It does **not** hold for a subproof introduced by
`process_simplify`'s `simplify_to_subproof` helper (used to elaborate `equiv_simplify` steps)
when that elaboration happens to sit *inside* another subproof's body — there, `pi3` is only the
sibling steps within that enclosing body, whose last step is just some arbitrary intermediate
derivation, not the true final conclusion. This was already flagged as suspect in the code
itself, in a comment on the old recursive call: `(* TODO: this line handles subproofs inside
subproofs but seems to generate checker failures. Need to verify. *)`.

Same failure signature as bug #1: every individual `Res`/`Weaken` step involved remains locally
valid (`Verit_Checker_Debug` reports no step failure), the certificate just no longer concludes
the empty clause.

**Fix:** rather than touching `process_subproof_aux`/`extend_cl` (both delicate, and used by
every subproof, not just the problematic nested ones), added `hoist_nested_subproofs`: a
self-contained structural pass that hoists every `SubproofAST` found nested inside another
`SubproofAST`'s body out to become that subproof's sibling, immediately preceding it —
recursively, so that no subproof's own body contains another one by the time `process_subproof`
runs. This is purely a reordering of steps in the flat list; ids are untouched and every
cross-reference between steps remains valid, since hoisted steps only move strictly earlier.
Once hoisted, a subproof's own `pi3` naturally extends through the formerly-enclosing subproof
and beyond, all the way to the true end, restoring the invariant `process_subproof_aux` depends
on. Wired into the pipeline right before `process_subproof`:
```
let c9' = hoist_nested_subproofs c9 in
let c10 = process_subproof c9' in
```

**Impact:** fixed the remaining 6 files that were returning `false` with no step failure
reported (all sharing the same shape: one `anchor`/subproof containing two `equiv_simplify`
steps in its body). Zero regressions.

---

## Final state

```
examples/regress:            433 total, 429 True/OK, 1 False, 3 Error, 0 Timeout
examples/aletheTests/sanitychecktests: test1–5 (cvc5 + veriT) all = true
```

### Known unresolved: `Green_cvc42/x2020_07_31_07_55_13_484_7016530cvc5.v` (1 `false`)

This file *also* has genuine (non-`simplify_to_subproof`) nested subproofs, and
`hoist_nested_subproofs` does change its behavior (the step `Verit_Checker_Debug` reports as
"likely failed" moves from 47 to 58 depending on whether the fix is applied), but it still
returns `false` either way. Extensively investigated without a conclusive fix:

- Hand-traced the reported-failing `Res` steps (and a parallel chain) directly — every one
  checks out correctly, including one case of harmless declared-vs-computed mislabeling that
  self-corrects downstream (same benign pattern as elsewhere in this codebase).
- Built a small OCaml-level fold-resolve simulator mirroring `State.v`'s `resolve`/`has_true`.
  It finds no ambiguous pivot points anywhere in the certificate, and predicts the whole thing
  resolves cleanly to the empty clause — disagreeing with the real checker.
- Ruled out (via direct research into `smtForm.ml`/`smtAtom.ml`) that `Iff(P, True)` gets
  canonicalized to `P` by any interning layer, which would have explained the "P vs Eq(P,true)"-shaped
  divergences the simulator flagged.
- Tried the simulator with symmetric-equality leniency disabled entirely (exact literal
  identity only) as a sanity check — it diverges from ground truth too, but in the opposite
  direction (predicts failure when the file does have some genuinely-required
  equality-direction collapses elsewhere), so neither extreme matches the real checker.

Conclusion: there's a real gap between this OCaml-level model of the checker's semantics and the
actual Coq-level behavior, not yet isolated. Given it's 1 of 433 files, this was set aside rather
than continuing to guess. A useful next step for a future session: compare against a possible
veriT-only proof of the same benchmark if one exists (isolates whether it's specific to cvc5's
proof shape), or instrument the actual Coq-level `resolve`/`has_true` computation directly rather
than re-modeling it in OCaml.

### Known unresolved, pre-existing, untouched: 3 `Error` files

All three fail on `cong_find_implicit_args`, which doesn't support congruence over integer
predicates (e.g. `<`, `<=` between integers). This is a separate, deeper limitation that predates
this session's work and wasn't investigated.

Root cause: `cong_find_implicit_args` calls `get_args_isfrms` on a `cong` step's conclusion to
work out the congruence's implicit argument-position equalities (e.g. for `f x T b = f y T a`
derived from `x=y` and `a=b`, it needs to know `f`'s argument list to line premises up with
positions). `get_args_isfrms` knows how to list arguments for `And`/`Or`/`Imp`/`Xor`/`Eq`/`Ite`/
`App`, but its very first match arm is `Lt (x, y) | Leq (x, y) | Gt (x, y) | Geq (x, y) -> raise
(Debug "congruence over integer predicates unsupported")` — congruence over an integer
inequality (e.g. proving `(>= a b) = (>= c d)` from `a=c` and `b=d`, which real cvc5 proofs do
routinely as part of normalizing linear arithmetic) just gives up immediately instead of listing
`[x; y]` the same way the `Eq` arm does one case above it. Two of the three files fail with this
exact message; the third fails with the closely-related "can't find implicit premise to congr"
once the same underlying gap is reached via a slightly different call path.

Worked example: [`cong_integer_predicate`](examples/aletheTests/claudeTests/cong_integer_predicate) —
unlike every other worked example in that directory, this one is **not fixed**; it's a minimal
reproduction (verified to raise the exact same `Debug` message, word-for-word, as the real
`examples/regress` failures) of a limitation nobody has fixed yet. A real fix would extend
`get_args_isfrms`'s `Lt`/`Leq`/`Gt`/`Geq` arm to return `[(x, is_frm x); (y, is_frm y)]` like the
`Eq` arm does, then verify `cong_find_implicit_args`'s downstream premise-matching logic (which
was written assuming `Eq`-shaped congruence) still lines premises up correctly for a
non-symmetric, non-`Eq` binary predicate.
