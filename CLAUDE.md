# Session summary: Alethe/veriT/cvc5 preprocessing fixes

This document summarizes uncommitted work on `src/verit/veritAst.ml`,
`src/verit/veritLexer.mll`, `src/verit/veritParser.mly`, and `examples/Makefile`, plus the new
`examples/regress/` regression suite. It's meant for review before committing, and as a record
of what was found and why each change was made.

**Net result:** the `examples/regress` suite (433 `.v` files: 5 small hand-picked tests +
`sledgehammer-benchmarks`, a large corpus of real cvc5/veriT proofs from Isabelle's Sledgehammer)
went from a state where a large fraction of the sledgehammer benchmarks either crashed outright
or produced a checked-but-wrong `= false`, to **433/433 passing** — no known-unresolved failures
left in the suite.

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
   have to trace which step's *computed* clause diverges from its *declared* one. Three distinct,
   unrelated root causes were found and fixed here (see "Correctness fixes" below):
   - an unsound premise being carried forward during recursive trivial-clause elimination
     (`process_trivial`). Worked example:
     [`trivial_unsound_premise`](examples/aletheTests/claudeTests/trivial_unsound_premise).
   - `process_subproof`/`process_subproof_aux`'s "recover hypotheses as facts using the rest of
     the proof" trick being invalid when the subproof it processes is itself nested inside
     another subproof's body. Worked example:
     [`nested_subproof`](examples/aletheTests/claudeTests/nested_subproof).
   - `process_same` unconditionally eliminating `symm`/`not_symm` steps by aliasing, which is
     unsound for a Boolean/`iff`-typed equality (only safe for a genuine first-order term
     equality). Worked example:
     [`symm_unsound_boolean_flip`](examples/aletheTests/claudeTests/symm_unsound_boolean_flip).

4. **The remaining errors.** `get_args_isfrms` didn't support congruence over integer predicates
   (`<`, `<=`, `>`, `>=`), causing 3 files to error out — fixed (see the `get_args_isfrms` section
   below). 2 of those 3 were then fully fixed by the `process_same` fix above (which resolved the
   `false` result the `get_args_isfrms` fix had merely uncovered); the 3rd hit a separate,
   *unrelated* limitation in `cong_find_implicit_args` itself: it had no way to handle a `cong`
   step over an n-ary `+`/`-`/`*` (3+ explicit premises, one per flat argument, matching real cvc5
   output) against `Plus`/`Minus`/`Mult`'s strictly-binary internal representation — fixed too
   (see "`cong_find_implicit_args`: n-ary `+`/`-`/`*` congruence" below). Worked examples:
   [`cong_integer_predicate`](examples/aletheTests/claudeTests/cong_integer_predicate),
   [`nary_arith_cong`](examples/aletheTests/claudeTests/nary_arith_cong).

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
A regression suite: 8 small hand-picked tests (`test1`–`test8`, cvc5 + veriT variants) plus
`sledgehammer-benchmarks/`, a large corpus of real proofs pulled from Isabelle's Sledgehammer
runs against cvc5 and veriT (439 `.v` files total). `calltests.sh` compiles every `.v` file
under it with `coqc` (each in its own directory, since the proof/SMT-LIB file paths inside are
relative), classifies each as `TRUE`/`FALSE`/`ERROR`/`TIMEOUT`, and prints a summary. This is
the harness used to find and verify every fix below — every fix was checked against the full
regression suite (plus `examples/aletheTests/sanitychecktests`) to confirm zero regressions
before being kept.

`test1`–`test5` were here from early on; `test6`–`test8` (copies of
`examples/aletheTests/sanitychecktests/test6`–`test8`, with `LoadPath` adjusted for the one
level's difference in nesting depth) were folded in once session 2's fixes brought all of
`sanitychecktests` to passing — the 433-file counts quoted through most of this document (from
before that point) reflect the suite without them; the true final count, with everything folded
in, is 439/439.

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

#### 3. `process_same`: unsound unconditional elimination of `symm`/`not_symm`

`symm`/`not_symm` alethe steps, parsed to `SameAST`, were previously always eliminated outright:
every downstream reference to the `symm` step's own id got rewritten straight to its premise's
id (`replace_prem`), on the theory that a clause and its symmetric-equality flip are "the same"
to the checker.

**The bug:** that's only true for a genuine first-order *term* equality — SMTCoq's atom
interning canonicalizes its direction via `Atom.mk_eq_sym` (confirmed directly in
`process_term_aux`'s `Eq` case in `veritAst.ml`: `mk_eq_sym` is reached only when both sides
intern as non-`Tbool` `Form.Atom`s). For a Boolean/`iff`-typed equality between two formulas,
`process_term_aux` instead builds a plain `Fiff` form, and `Fiff`'s own hash-consing
(`HashedForm.equal` in `smtForm.ml`) compares arguments *positionally*, with no normalization of
order — so `Eq(P,Q)` and `Eq(Q,P)` are two distinct, order-sensitive literals there. Blindly
aliasing the `symm` step's id to its un-flipped premise silently feeds the wrong-direction
literal into any downstream step that specifically needed the flip to find its resolution pivot
— found via a real sledgehammer-benchmarks proof where cvc5 emits an explicit `symm` step to
flip an `all_simplify`-produced equality before combining it with an `equiv_pos2` step that
needs the other direction. Same failure signature as bugs #1 and #2: every individual step
remains locally valid (`Res` steps are unconditionally sound regardless of which pivot, if any,
they find), so `Verit_Checker_Debug` reports no step failure — the certificate just silently
stops concluding the empty clause.

**Fix:** added `eq_is_symmetrized`, which mirrors `process_term_aux`'s own `Eq` case to detect
whether a given equality is a genuine, direction-canonicalized term equality. When it isn't,
`process_same` now builds an explicit, checker-verified derivation of the flipped clause (a new
`build_eq_symm_tautology` helper deriving the tautology `~(p=q) \/ (q=p)` via the
`Equp1`/`Equp2`/`Equn1`/`Equn2` axiom-resolution pattern used throughout `process_cong`) instead
of aliasing ids.

Getting the axiom shapes right needed care: an earlier draft of this fix (verified to fix its 2
target files) caused a large regression (16 files, including the simplest sanity tests) because
`Equp1AST`/`Equp2AST`'s exact literal polarities were transposed. The correct shapes were
re-derived directly from the Coq-level checker (`check_BuildDef`/`check_BuildDef2` in
`src/cnf/Cnf.v`, not just the OCaml-side CNF generator in `smtCnf.ml` — the checker recomputes
each step's clause fresh from its first literal alone, ignoring the rest of what's declared, so
the shape must match the checker byte-for-byte) and cross-checked against existing, tested,
non-degenerate usages elsewhere in `process_cong`.

A second, narrower issue surfaced during regression testing: `SameAST` is overloaded in the
parser — it's produced not just for `symm`/`not_symm` but also for `cont` (contraction),
`reordering`, and `factoring`, none of which carry any equality-direction meaning (they just
restate an earlier clause's literals, deduplicated/reordered, for which aliasing is always
sound regardless of clause shape). Since `SameAST` doesn't record which of these five rules
produced it, `process_same` now only takes the new direction-aware path when the clause is
unambiguously a singleton equality that isn't already direction-safe, falling back to the old,
always-sound aliasing for anything else (multi-literal clauses, or a singleton that isn't an
equality) — this exact gap broke a sanity test (`test4`, which uses `reordering`) during
development.

A third issue surfaced empirically: building the full tautology derivation for a `symm` step
whose equality involves a bare Boolean constant (`true`/`false`) made `test1` (and only `test1`)
return `false`. The first fix attempt was a pragmatic dodge — `eq_safe_to_alias` fell back to the
old (in-general-unsound) aliasing whenever either side of the equality was a bare `true`/`false`
constant — but follow-up investigation (below) showed this dodge wasn't actually sound either
(confirmed via a faithful minimal reduction of `test1`'s shape closed with plain `resolution`
instead of `test1`'s own `trans`: it *still* returned `false` even with the fallback in place,
because `trans`'s premise-reordering happens to tolerate either direction while `resolution`
doesn't). That dodge has since been replaced by the real fix, described next.

**Root-cause investigation and the real fix.** Asked to find a general fix rather than live with
the aliasing dodge, the first thing this surfaced is that the bug isn't specific to `process_same`
at all: a `:rule trans` step, using `process_trans` directly (existing, tested, long-standing
code, completely bypassing anything added this session), failed identically on the exact same
`(not true)`/`false` pair.

Pinning down the actual mechanism required more than reading source and hand-simulating the
checker — that approach hit real dead ends (e.g. a hypothesis that literal `0`, the checker's
reserved "give up" sentinel `Lit._true`, collides with genuine positive occurrences of the `true`
atom via `State.v`'s `insert`/`C._true` short-circuit turned out to be unreachable from the main
checking path, since `S.set`'s `sort` call uses `insert_no_simpl`, not `insert`). So a new
diagnostic tool was built: **`Verit_Checker_Trace <smt2> <cvc5pf>`** (mirrors
`Verit_Checker_Debug`'s invocation), added via:
- `Trace.v`: a new `Euf_Checker.checker_trace` definition (plus its `Register ... as ...` line,
  required for `Coqlib.lib_ref`-based OCaml lookup - easy to miss, cost real time here) that,
  unlike `checker_debug` (which stops at the first "likely failed" step and only reports a step
  *number*, established earlier this session as unreliable to map back to source), walks every
  step and returns the checker's own freshly-computed clause (raw literal ints, not the
  OCaml-side declared one) at each one, plus the root clauses and final answer position.
- `smtCommands.ml`/`coqTerms.ml`/`verit.ml`/`g_smtcoq.mlg`: OCaml plumbing mirroring
  `checker_debug`'s existing pattern, but printing the raw result via Coq's own pretty-printer
  (`CoqInterface.pr_constr_env`) instead of decoding it - avoids writing a custom Coq-value
  decoder entirely.

Tracing the minimal `(not true)`/`false` reproduction with this tool showed the derivation's
final answer clause was `[4; 0]` - literal `4` was `a0`'s own *unflipped* fact, literal `0` was
`Lit._true` (the give-up sentinel) - and, critically, that only 2 real Coq-level steps existed for
what should have been a ~9-step derivation (`x1..x7,t1,t2`). That was the actionable clue: OCaml's
`process_unused` pass showed the SAME shrinkage, and dumping the certificate immediately before it
(right after `process_trivial`) showed why - **`process_trivial` had eliminated `x3`, `x6`, and
`x7` entirely as a "trivial" clause** (one containing some literal and its negation), replacing
`t1`'s two-premise resolution (`[x7; a0]`) with a single-premise one (`[x9]`, a `Weaken` of `a0`
alone). A single-premise `:rule resolution`, per `VeritSyntax.mk_clause`'s `Reso` case, compiles
to `Same` - a pure id alias, not a genuine resolve - so `t1` silently became an alias for `a0`'s
own *unflipped* clause, discarding the derivation's entire purpose.

`process_trivial`'s trivial-clause detection (`neg_mod_dneg_symm`, built on `eq_mod_dneg_symm`)
already had - and needed - the same kind of guard as `eq_is_symmetrized`: for a *Boolean/`iff`*
equality, `Eq(P,Q)` and `Eq(Q,P)` are NOT interchangeable, so a clause containing
`Not(Eq(P,Q))` and `Eq(Q,P)` must not be treated as a complementary (trivial) pair the way it
correctly would be for a genuine first-order term equality. `eq_mod_dneg_symm`'s `Eq,Eq` case
*did* have exactly this guard (an inline `is_term` helper) - but its fallback branch was backwards:

```ocaml
let is_term = (fun x -> match snd (process_term_aux x) with
                        | Form.Atom h -> (match Atom.type_of h with Tbool -> false | _ -> true)
                        | _ -> true) in   (* WRONG - should be false *)
```

`is_term`'s job is "does this operand intern as a genuine first-order term atom" (only then is
the equality's direction canonicalized and safe to treat as symmetric). But its fallback,
`| _ -> true`, defaulted to "yes, treat as a term" for anything that *doesn't* intern as
`Form.Atom` at all - which includes bare Boolean constants (`True`/`False` intern as `Form.Form`)
and negated/compound formulas (intern as `Form.Lit`/`Form.Form`). So whenever *both* sides of a
Boolean equality happened to be constant-or-negated-constant - exactly `(not true)` vs `false` -
`is_term` wrongly returned `true` for all four operands, `eq_mod_dneg_symm` wrongly allowed the
symmetric (flip-permitted) comparison, and `process_trivial` wrongly judged `Not(Eq(P,Q))` and
`Eq(Q,P)` as complementary. Bare declared Boolean *variables* never hit this, since they DO intern
as `Form.Atom` and take the correct branch - which is exactly why every earlier reproduction using
a plain variable on one side worked fine, and only the both-sides-constant shape broke.

**Fix:** flip the fallback to `| _ -> false`, matching `eq_is_symmetrized`'s already-correct
convention. With this in place, `process_trivial` no longer wrongly eliminates the derivation, and
the earlier `eq_safe_to_alias`/`is_bool_const` dodge in `process_same` is no longer needed at all -
removed entirely, so `process_same` now just calls `eq_is_symmetrized` directly.

**A separate, still-open issue found along the way:** `process_trans` itself - independent of this
fix, and of `process_trivial` - also fails on a raw `:rule trans` over `(not true)`/`false` (no
`symm` involved). Tracing shows `process_trans`'s own axiom-construction produces a degenerate
single-premise result directly (`t1 = Res[a0]`, immediately aliased same as above) rather than
building the expected multi-step derivation - a different bug in `process_trans`'s "reord" branch
(which already looked suspicious earlier: it tags content matching `Equp1AST`'s ground-truth shape
with the `Equp2AST` tag, a mismatch never fully reconciled). This is *not* fixed by the
`is_term` fix above, and is not exercised by anything in `examples/regress` (no real proof asks
`trans` to flip a bare-constant equality) - a genuine, separate, lower-priority gap, left for a
future session; `Verit_Checker_Trace` is the tool to pick it back up with.

**Impact:** fixed all 3 remaining `false` files in the suite, including
`Green_cvc42/x2020_07_31_07_55_13_484_7016530cvc5.v` (previously investigated extensively and
set aside as unresolved — see git history for that investigation's details) and the 2
`HOL-Library` `BuildDef2` files the `get_args_isfrms` fix below had merely uncovered (see that
section). Zero regressions across the full 433-file suite plus
`examples/aletheTests/sanitychecktests`. Worked example:
[`symm_unsound_boolean_flip`](examples/aletheTests/claudeTests/symm_unsound_boolean_flip).

---

## Final state

```
examples/regress:            433 total, 433 True/OK, 0 False, 0 Error, 0 Timeout
examples/aletheTests/sanitychecktests: test1–5 (cvc5 + veriT) all = true
```

### `get_args_isfrms`: congruence over integer predicates (`<`, `<=`, `>`, `>=`)

**Bug:** `cong_find_implicit_args` calls `get_args_isfrms` on a `cong` step's conclusion to work
out the congruence's implicit argument-position equalities (e.g. for `f x T b = f y T a` derived
from `x=y` and `a=b`, it needs to know `f`'s argument list to line premises up with positions).
`get_args_isfrms` knows how to list arguments for `And`/`Or`/`Imp`/`Xor`/`Eq`/`Ite`/`App`, but its
`Lt`/`Leq`/`Gt`/`Geq` arm just raised `Debug "congruence over integer predicates unsupported"`
unconditionally — congruence over an integer inequality (e.g. proving `(>= a b) = (>= c d)` from
`a=c` and `b=d`, which real cvc5 proofs do routinely as part of normalizing linear arithmetic)
gave up immediately instead of listing `[x; y]` the same way the `Eq` arm does one case above it.

**Fix:** extended that arm to return `[x; y]` (tagged formula-vs-term the same way `Eq` does).
This is sound despite inequalities not being symmetric like `=` is, because nothing downstream
treats the relation as symmetric on `get_args_isfrms`'s account: `cong_find_implicit_args`'s own
symmetry-aware argument reversal is pattern-guarded to `Eq(_,_)` specifically (never fires for
inequalities), and the actual derivation this enables — `EqcpAST`, the fixed axiom
`x=a -> y=b -> P(x,y) -> P(a,b)` — is a generic substitutivity schema that holds for *any*
predicate `P`, symmetric or not.

**Impact.** Of the 3 `examples/regress` files that failed on this exact limitation:
- `HOL-Library/smt_verit/x2020_07_24_00_32_10_259_5099720cvc5.v` still errored at the time,
  unaffected: it hits the closely-related `cong_find_implicit_args.f: can't find implicit premise
  to congr` message via a different call path than the one this fix touches — confirmed by
  testing it before and after: identical error, byte-for-byte, both times. Root-caused and fixed
  separately — see "`cong_find_implicit_args`: n-ary `+`/`-`/`*` congruence" below.
- `HOL-Library/smt_cvc4/x2020_07_23_16_01_56_200_5114158cvc5.v` and
  `HOL-Library/smt_verit/x2020_07_23_15_35_20_861_5083584cvc5.v` no longer crash during
  preprocessing, but at that point ran to completion and returned `false` instead of `true` —
  a *different*, previously-masked bug this fix's crash had been hiding (`Verit_Checker_Debug`
  reported `Step number 30 (BuildDef2) of the certificate likely failed` for both — same step,
  consistent with these two being cvc4/veriT proof variants of the same underlying Isabelle
  lemma). Root-caused and fixed separately — see `process_same`'s correctness fix above; both
  files now pass.

Net effect on the suite: this fix alone changed `False` 1→3 and `Error` 3→1 (uncovering, not yet
fixing, two further bugs); combined with `process_same`'s fix and `cong_find_implicit_args`'s
fix below, the suite is now at 433/433 True/OK.

Worked example: [`cong_integer_predicate`](examples/aletheTests/claudeTests/cong_integer_predicate) —
verified to hit the exact same `Debug` message, word-for-word, as the real `examples/regress`
failures before this fix, and to pass after it.

### `cong_find_implicit_args`: n-ary `+`/`-`/`*` congruence

**Bug:** cvc5 emits a `cong` step over an n-ary `+`/`-`/`*` with one explicit premise *per flat
argument* — e.g. `(+ a b c) = (+ a' b' c')` derived from 3 premises `a=a'`, `b=b'`, `c=c'`. But
`Plus`/`Minus`/`Mult` are strictly binary constructors here (`veritParser.mly` left-folds n-ary
`+`/`-`/`*` into nested binary applications at parse time — see the `veritParser.mly` section
above), so `get_args_isfrms` only ever reports 2 arguments for such a node, however many premises
cvc5 actually supplied. `cong_find_implicit_args`'s normal matching — walk argument positions
one at a time, consuming at most one explicit premise per position, falling back to implicit
reflexivity for any position where the argument is syntactically unchanged — has no way to
consume 3+ premises against a 2-argument node: once it runs out of *positions* while premises
remain, it gives up with `cong_find_implicit_args.f: can't find implicit premise to congr`, the
one error left in the suite (`HOL-Library/smt_verit/x2020_07_24_00_32_10_259_5099720cvc5.v`,
step `t6`: exactly this shape, `(+ e1_d (* -1 e2_d) (* -1 (+ e1_d (* -1 e2_d)))) = ...` derived
from 3 premises against cvc5's own 3-ary `+`).

**Fix:** a new `fold_nary_arith_prem`, called whenever `fx`/`fy` are both `Plus`/`Minus`/`Mult`
and there are more than 2 premises. Since our left-folded term is `Plus(Plus(...,argN-1),argN)`
and premise `k` (1-indexed) proves flat argument `k`'s equality (cvc5's own convention), this
recursively folds the first `n-1` premises against the left subtree — inserting one synthetic
`EqcoAST`+`ResoAST` congruence step per fold, in the exact shape `process_cong`'s own "no implicit
equalities" case already builds for a genuine 2-ary node (and confirmed correct by that code's
own passing tests, e.g. this same file's `t12`/`t15`, real 2-ary `+`/`>=` congruences) — down to
exactly one combined id+equality for the left subtree, which is then paired with the untouched
last premise as the *2* logical premises `Plus`/`Minus`/`Mult`'s own binary structure needs. That
pair is handed back as `cong_find_implicit_args`'s ordinary return value, so the rest of the
(already correct) machinery — including the top-level `process_cong` caller that builds the
final, outermost congruence step — runs completely unchanged.

Getting the emitted certificate's step *order* right needed a fix of its own during testing: a
first draft built each fold's two new steps by consing them onto the front of the recursively-
obtained step list (`newstep :: recursive_steps`), which put a step *before* the dependency
(from the recursive, deeper fold) that it itself resolves against — `VeritSyntax.mk_clause`
failed with `get_clause: clause number ... not found` when it tried to process the later step
before its premise had been inserted. Fixed by appending instead (`recursive_steps @ [newsteps]`),
matching the forward, dependency-first ordering `build_eq_symm_tautology` (this session's other
multi-step derivation-builder) already uses, and that every caller of this kind of step-list
already expects (each consumed via `List.rev_append` onto a reverse accumulator).

**Impact:** fixes the single remaining `examples/regress` `Error`. The suite is now **433/433**,
verified with zero regressions. Worked example:
[`nary_arith_cong`](examples/aletheTests/claudeTests/nary_arith_cong) — verified to hit the exact
same `Debug` message as the real failure before this fix (a minimized version of the same shape:
3 explicit premises for a 3-ary `+`, written with explicit double-nesting - `(+ (+ a b) c)` - in
the smt2 file's own assertions specifically to stay clear of a separate, pre-existing, unrelated
limitation: `smtlib2_genConstr.ml`, the parser for the *smt2 file's own* root assertions, only
recognizes binary `+`/`-`/`*`, unlike `veritParser.mly`'s proof-file parser which already
handles n-ary via left-folding; not investigated further since it isn't exercised by anything in
`examples/regress` and wasn't part of what this fix needed to address), and to pass after it.

---

## Session 2: fixing the sanity-check suite (`examples/aletheTests/sanitychecktests`)

Follow-on session, after `examples/regress` reached 433/433. `sanitychecktests` (`test1`–`test8`,
cvc5 + veriT variants, `Notes.md` in that folder) is a separate, much smaller, hand-picked suite
that predates `examples/regress` and exercises different proof shapes (in particular, heavy use
of `hole :args (ARITH_POLY_NORM ...)` for arithmetic normalization, and deeply nested
`ite`/`and`/`imp` structure from `bool_simplify`/`all_simplify` elaboration). Three of its
tests were still failing going into this session: `test6cvc5`, `test7verit`, `test7cvc5` (plus
`test8cvc5`, which turned out to share `test7cvc5`'s root cause). **Net result: all 8 tests now
pass** (`test1`–`test5`, `test6cvc5`/`test6verit`, `test7cvc5`/`test7verit`,
`test8cvc5`/`test8verit`), verified with a full, clean 433/433 `examples/regress` run on top —
zero regressions from either fix below.

### `src/lia/lia.ml`: `Fiff`/Micromega representation mismatch

**Bug:** `smt_Form_to_coq_micromega_formula` (the OCaml-side translator from SmtCoq's `Form.t` to
Micromega's certificate-construction formula type, used when building a `hole
:args (ARITH_POLY_NORM ...)` step's LIA certificate) translated `Fapp (Fiff, [f1; f2])` using
Micromega's own native `IFF` constructor. But `Lia.v`'s *check-side* `build_hform` — which
re-derives the same formula from scratch when *verifying* the certificate — has no `Fiff` case
using `IFF` at all; its `Fiff a b` case manually expands to
`AND (OR f1' (NOT f2')) (OR (NOT f1') f2')`. A LIA certificate is built (in OCaml) against
whichever CNF shape `tauto_lia`'s own conversion of the *build-side* formula produces; if the
build-side formula uses a differently-structured connective than the check-side formula for
the *same* logical content, Micromega's certificate — sound only against its own CNF, not up to
logical equivalence — doesn't verify against the check-side's different CNF shape. Concretely:
whenever an `ARITH_POLY_NORM` fact's top-level shape was an iff-of-equalities (e.g.
`(y = (1+x)) = (x = ((-1)+y))`, or the degenerate `(not true) = false`), the OCaml side built a
certificate for `IFF(...)`'s CNF while the Coq side re-derived and checked against
`AND(OR,OR)`'s CNF — a structural mismatch, not a certificate-strength problem, so the check
simply failed regardless of how good the underlying LIA reasoning was.

**Fix:** changed the `Fapp (Fiff, l)` case to manually construct
`AND (IsProp, OR (IsProp, f1, NOT (IsProp, f2)), OR (IsProp, NOT (IsProp, f1), f2))`, mirroring
`build_hform`'s Coq-side expansion exactly instead of using Micromega's `IFF`.

**Impact:** this single fix resolved **two** of the three failing tests directly —
`test8cvc5` (whose `hole`-heavy proof hits exactly this shape at several steps) and,
unexpectedly, `test7cvc5` too (originally flagged by the user as the one most likely to need an
"involved solution" and saved for last — it turned out to be fixed as an incidental side effect
of this same root-cause fix, needing no dedicated work of its own once this was found).
Verified via 4 hand-built minimal reproductions (an iff-of-term-equalities case, the simplest
possible `(x=y)=(y=x)`, a genuine-non-tautology control case confirmed to still correctly fail,
and a `(x=y)=((x-y)=0)` case) before touching the real tests, then against `test7cvc5`/`test8cvc5`
themselves, then against the full 433-file `examples/regress` suite (zero regressions).

### `src/verit/veritAst.ml`, `extend_cl_aux`: `Nequ2AST` axiom polarity

**Bug:** the `Nequ2AST, Not (Eq (x, y))` case of `extend_cl_aux` (used when a subproof-discharge
needs to re-derive an axiom-clause form of a premise's negated equality) declared
`(Equn1AST, [Eq (x, y); x; Not y])`. Per this session's independently-verified ground truth for
these axiom shapes (cross-checked against `check_BuildDef`/`check_BuildDef2` in `src/cnf/Cnf.v`
and existing, tested, non-degenerate usages elsewhere in `process_cong`),
`Equn1AST(A,B) = [Eq(A,B); Not A; Not B]` — the declared clause had `A` (`x`) instead of `Not A`
(`Not x`) as its second literal, an outright polarity error.

**Fix:** `(Equn1AST, [Eq (x, y); Not x; Not y])`.

**Impact:** a genuine, independently-confirmed correctness fix (verified against the full
433-file suite plus all 8 sanity tests, zero regressions) but not, on its own, sufficient to
resolve any test that was still failing at the time it was found — kept regardless, since an
incorrect axiom-shape declaration is a latent bug even when nothing currently exercises the
specific path that would expose it.

### `src/verit/veritAst.ml`, `process_cong`'s `Or`-congruence case: premise-fold ordering

**Bug:** `test6cvc5` (and, independently, `test7verit`) kept returning `false` after both fixes
above, with no individual step ever flagged as invalid by `Verit_Checker_Debug` — the same
"checks out step-by-step but doesn't conclude the empty clause" signature as the three
correctness bugs fixed in the previous session (`process_trivial`'s `pids`, `process_subproof`'s
nested-subproof `pi3`, `process_same`'s unconditional `symm` aliasing). Diagnosing it needed a
new tool: **`Verit_Checker_Trace`**, which walks every checker step and dumps its *actual,
freshly-computed* clause (raw literal ints) rather than the declared/OCaml-side one — added via
a new `Euf_Checker.checker_trace` in `src/Trace.v` plus OCaml plumbing mirroring
`Verit_Checker_Debug`'s existing pattern in `src/trace/smtCommands.ml`/`coqTerms.ml`/
`src/verit/verit.ml`/`src/g_smtcoq.mlg`. Tracing `test6cvc5` showed the final computed clause was
`[_true; _true]` (the checker's give-up sentinel, twice) instead of empty, and pinpointed the
first step where a `_true` literal appeared: a 6-premise `Res` step built by `process_cong`'s
`Eq (Or xs, Or ys)` case, deriving one direction of an Or-congruence over 3 disjuncts.

That builder (see the code's own numbered comments) constructs, for `x1 ∨ x2 ∨ x3 = y1 ∨ y2 ∨ y3`:
an `orp` unfold of the source `Or`, then — as two *separate, grouped* batches — every changed
disjunct's `eqp2`-based substitution fact (`xi → yi`), followed by every disjunct's `orn`-based
projection fact (`yi → Or ys`), all folded together via one N-ary `Res`. In `test6`'s specific
instance, disjunct 2 (`Not (g (f x))`) is *unchanged*, while disjunct 3 substitutes to `g (f x)`
*positively* — i.e. the *substituted* value of one disjunct happens to coincide, up to negation,
with the *unchanged* value of a different, unrelated disjunct. SmtCoq's checker-side `resolve`
(`src/State.v`) is a sorted-merge, single-pivot-per-pairwise-fold algorithm: given two clauses,
it scans in sorted literal order and stops at the *first* complementary pair it finds, merging
everything else via a dumb union (`or`) with no further cancellation. When the grouped ordering
hands a single fold step *two* simultaneous valid complementary pairs (the intended one, plus
this accidental cross-disjunct collision), `resolve` cancels whichever sorts first and leaves the
other pair's literals stuck, uncancelled, in the result — residue that nothing downstream happens
to clean up, ultimately collapsing the derivation to `_true` instead of the declared clause. Every
individual step stays locally valid (a `_true` weakening is still sound), so nothing crashes and
`Verit_Checker_Debug` reports no failing step — exactly the established "checks out, wrong answer"
signature.

**Fix:** rebuilt the premise list to interleave *by disjunct position* instead of by phase: for
each position `k` in turn, emit (if the disjunct changed) its `eqp2`/`eqp1` substitution fact
immediately followed by its own `orn` projection fact, before moving to position `k+1` — rather
than "all substitution facts, then all projection facts". This guarantees each position's
temporary literals are fully consumed (replaced by `Or ys`/`Or xs`) before a *later* position can
introduce a value that might collide with an *earlier*, not-yet-processed literal, so no single
two-clause fold is ever handed more than one complementary pair. Applied symmetrically to both
directions of the derivation (`resi1`'s `eqp2`/`ornis1` and `resi3`'s `eqp1`/`ornis2`). As a
simplification enabled by the same rewrite, the `orn` projection facts are now built directly via
`List.mapi` over the (non-deduplicated) argument list at each position, rather than deduplicating
via `to_uniq`/`findi` first — `OrnAST`'s projection is inherently positional, so per-position
generation needs no separate value-based lookup, and a redundant extra projection fact for a
duplicate value is harmless (merges away same as any other case).

**Impact:** fixes `test6cvc5` (confirmed via the `Verit_Checker_Trace`-observed `[_true; _true]`
residue before the fix). Verified against the full 433-file `examples/regress` suite, zero
regressions. Worked example:
[`or_cong_collision`](examples/aletheTests/claudeTests/or_cong_collision) — a standalone copy of
`test6cvc5`'s exact proof shape, confirmed to return `false` before this fix and `true` after it.

**Correction:** `test7verit` was *initially* (incorrectly) reported fixed by this same change too,
based on it also hitting `false → true` in one run — that was a verification mistake (checking
`coqc`'s exit code and `.vo` production, neither of which catches `Verit_Checker` completing
"successfully" while still printing `= false`; the correct check, matching what
`examples/regress/calltests.sh` itself does, is grepping the output for `= true`/`= false`, since
`Verit_Checker`, unlike a hard `Qed`, does not fail the file just because the checker computed
`false`). Caught when the user re-ran `sanitychecktests/calltests.sh` directly. `test7verit` was
still failing at the time; re-diagnosing it led to the `Reso`/`ThReso` investigation below
(itself later found to have been chasing a false lead), and eventually to the `Ite1AST` and
`mkCongrPred` fixes further down, which are what actually got it passing.

### Dead end investigated and ruled out: `mk_clause`'s `Reso`/`ThReso` premise order

Re-diagnosing `test7verit`'s `t6` (`th_resolution :premises (h1 t2 t5)`) by hand-decoding the
checker's own literal integers (`Form.to_lit`, `is_pos = is_even`) for `h1`, `t2`, `t5` appeared
to show that resolving premises in veriT's *listed* order has no valid pivot between `h1` and
`t2`, and that a general fix — reordering `Reso`/`ThReso`'s premise list so each fold always has
a pivot before calling `C.resolve` (`State.v`), which otherwise gives up and collapses to the
checker's `C._true` sentinel — was needed. That diagnosis missed that `Threso`'s handling
(unlike `Reso`'s) already reverses the premise list via `List.rev` *before* folding: the actual
fold order is `t5, t2, h1`, not `h1, t2, t5`, and re-simulating against that *real* order finds a
clean pivot at every step — `t6` was never actually broken. A fix along these lines was built and
briefly kept (verified sound, zero regressions) before this was caught; once caught, it was
reverted rather than kept as unused insurance, per the standing project preference to avoid
touching `veritSyntax.ml` (a file shared by every proof rule) without a demonstrated need.
`test7verit`'s real remaining failures were the `Ite1AST` and `mkCongrPred` bugs below.

### `src/verit/veritAst.ml`, `extend_cl_aux`'s `Ite1AST` case: wrong `ite` branch index

**Bug:** `extend_cl_aux`'s `Ite1AST, Ite xs -> (Itep1AST, [Not (Ite xs); List.nth xs 0; List.nth
xs 1])` case (used when `extend_cl` needs to re-derive an axiom-clause form of a `:rule ite1`
step that turned out to (in)directly depend on an eliminated subproof's own conclusion) used
`List.nth xs 1` — the `ite`'s *then*-branch — for `Itep1AST`'s third literal. But veriT's own
`ite_pos1` axiom (which `Itep1AST` represents) is `[Not(ite c t e); c; e]` — the *else*-branch,
`List.nth xs 2` — confirmed directly from `test7verit.pf`'s own raw, directly-parsed `ite_pos1`/
`ite_pos2`/`ite_neg1` facts (`t19`/`t20`/`t21`), which unambiguously put the else-branch third.
The three sibling cases (`Nite1AST`→`Iten1AST`, `Ite2AST`→`Itep2AST`, `Nite2AST`→`Iten2AST`)
already used the correct index each; only this one didn't.

Found by extending the from-scratch `Verit_Checker_Trace`-based diverge-finder (see the previous
section) to compare, for *every* step, its checker-side freshly-computed clause against its
declared one — the first real divergence was `x149`, a synthetic `Itep1AST` fact for a *nested*
`ite` (`ite op_0 (ite op_1 ...) (ite op_1 ...)`, from `test7verit`'s `t22`, `:rule ite1
:premises (t18)` — `t18` itself indirectly depends on an eliminated `bool_simplify` subproof,
routing `t22` through exactly this `extend_cl_aux` case). Its declared "then" literal (var 24 in
that run) didn't match what the checker's own `check_BuildDef`-family reconstruction of the same
`Ite` formula computed at the same position (var 28) — not a polarity flip, a *different atom*,
consistent with reading the wrong argument index out of `xs` entirely.

**Fix:** `List.nth xs 1` → `List.nth xs 2` in the `Ite1AST` case only.

**Impact:** confirmed via the diverge-finder that `x149` (and everything chained through it) no
longer diverges. `test7verit` still returned `false` at this point — see the next section for
the second, independent remaining bug. Verified zero regressions against the full 433-file
`examples/regress` suite plus all sanity tests. No dedicated worked example (see
`examples/aletheTests/claudeTests/README.md` for why); verified via `test7verit` itself.

### `src/verit/veritSyntax.ml`, `mkCongrPred`: `concl`/`prem_P` picked by position instead of polarity

**Bug:** `mkCongrPred` (handles veriT's `eq_congruent_pred` rule, which proves a predicate
congruence clause `[¬(p1=p1'); ...; ¬(pn=pn'); ¬P(p1,...,pn); P(p1',...,pn')]` — hypothesis
equalities negated, the old predicate occurrence negated, the new one asserted positively) picked
out the clause's last two literals by fixed *position*: `List.rev p`'s first element was always
assumed to be `concl` (the positive, new-argument occurrence) and the second always `prem_P` (the
negative, old-argument occurrence). veriT doesn't guarantee that order for a non-symmetric
predicate: in `test7verit`'s `t58` (`:rule eq_congruent_pred`, over `<=`), the clause is `[¬(a=c);
¬(b=d); (a'≤b'); ¬(a≤b)]` — the *positive* new occurrence comes *before* the *negative* old one,
the reverse of what the old position-only code assumed. That silently swapped `concl`⇄`prem_P`,
so `process_congr` (called with `Atom.atom (get_at c)`/`Atom.atom (get_at p_p)` for the now-wrong
`c`/`p_p`) built the congruence hypotheses' argument correspondence backwards — `t58` still built
*some* certificate (no crash, no `Debug` exception), just not the sound one, so the checker's own
independent recomputation for `t58` diverged from declared (same "checks out, wrong answer"
signature throughout this document): declared `[¬35-ish; ¬41-ish; 85; 87]` vs. checker-computed
`[+35-ish; +41-ish; 85; 87]` — both changed literals flipped polarity together, consistent with
`concl`/`prem_P` (and hence the two predicate arguments' old/new roles) being swapped as a pair,
not an independent single-literal bug.

**Fix:** pick `concl`/`prem_P` from the last two literals by polarity (`Form.is_pos`) instead of
fixed position — whichever of the two is positive is `concl`, the other is `prem_P`. (A second,
polarity-based implementation of `mkCongrPred` already existed in this file, entirely commented
out and calling an unused, seemingly-abandoned `process_congr_form` helper — not reused, since it
looked incomplete; this fix is a minimal, targeted change to the *active* implementation instead.)

**Impact:** fixes `test7verit`'s `t58` divergence — with both `Ite1AST` and this fix applied,
`test7verit` returns `true`. Verified against the full 433-file `examples/regress` suite plus all
8 sanity tests (`test1`–`test8`, cvc5 + veriT where applicable), zero regressions. Worked example:
[`eqcongruentpred_polarity`](examples/aletheTests/claudeTests/eqcongruentpred_polarity) — a
minimal, standalone, hand-written `eq_congruent_pred` step over `<=` with the same "positive
before negative" literal order, confirmed to return `false` before this fix and `true` after it
(the old, positional code was temporarily restored and re-verified to reproduce the failure
before finalizing this fix, rather than relying only on the reasoning above).

### Final state (session 2)

```
examples/regress:                       439 total, 439 True/OK, 0 False, 0 Error, 0 Timeout
examples/aletheTests/sanitychecktests:  test1-8 (cvc5 + veriT where applicable) all = true
```

No known-unresolved failures left in either suite as of this writing. `test7cvc5` ended up fixed
as an incidental side effect of the `Fiff`/Micromega fix (see above), needing no dedicated work
of its own; `test7verit` needed exactly two fixes (`extend_cl_aux`'s `Ite1AST` index and
`mkCongrPred`'s polarity) — a third, a `mk_clause` premise-reordering fix, was investigated and
briefly built along the way but turned out to be chasing a false lead (see "Dead end investigated
and ruled out" above) and was reverted, not kept — consistent with the original `Notes.md`
assessment that `test7` "might need an involved solution."

---

## Session 3: `examples/aletheTests/QFUFTests` fixes

Follow-on session. `examples/aletheTests/QFUFTests/otherSummary.md` records the categories of
files that fail when the checker is run over a much larger (~7,468-file) real-world corpus than
`examples/regress`'s own sledgehammer-benchmarks; each category folder there (`get_clause`,
`findi`, `get_eq`, `subproof`, `cong`, `trans`, plus the out-of-scope `invalid*`/`parserError`
character-encoding and parser-coverage categories) holds 2–3 representative benchmark files. This
session worked through `get_clause`, `findi`, `get_eq`, `subproof`, and `cong`/`trans` (skipping
`invalid*`/`parserError` as instructed — those are lexer/parser-coverage gaps, not checker bugs).

**Net result:** three genuine, general bugs fixed in `process_trivial` (all in
`src/verit/veritAst.ml` — `src/verit/veritSyntax.ml` was not touched this session, consistent with
the standing preference to leave that shared file alone absent a demonstrated need). All three were
found by the same pattern that's recurred throughout this document: a benchmark that used to crash
outright now runs to completion, and the fix is verified sound against the full 439-file
`examples/regress` suite plus all 8 `sanitychecktests` (zero regressions in both). Several of the
category's benchmarks still return `false` after their crash is fixed — each such case was traced
to a *different*, deeper, unrelated bug and is documented below as a known limitation rather than
papered over.

### 1. `process_trivial` eliminating a clause a `tautology` step still needs

**Bug:** `process_trivial` treats any clause containing some literal and its negation as
"trivial" and removes it, patching every `resolution`/`th_resolution` consumer it can find via
`find_res` (which only looks at `ResoAST`/`ThresoAST` steps) to no longer depend on it. But a
`tautology` step (`TautAST`) is checked completely differently: `VeritSyntax.mk_clause`'s `Taut`
case builds `Tautology (get_clause i, l)`, which the Coq-side checker (`check_Tautology` in
`src/cnf/Cnf.v`) verifies by reading the premise clause `i`'s own, unmodified content directly and
checking *it itself* contains a complementary pair — it isn't a resolution that could be
re-derived from a substitute. `find_res` doesn't know about `TautAST`, so a trivial clause feeding
a `tautology` step downstream gets eliminated exactly as if nothing depended on it, and the
`tautology` step is left citing an id that no longer exists in the output certificate —
`VeritSyntax.Debug`, `get_clause: clause number ... not found`.

**Fix:** a new `used_as_taut_premise` guard added to the top-level "is this clause trivial"
match in `process_trivial_aux`, checking whether any `TautAST` step downstream cites this clause
directly as a premise. Extended to `taut_protected`, which also follows the protection
*transitively* through single-premise `Reso`/`Threso` "alias" steps (which `mk_clause` compiles to
a pure id alias, `Same`, since a lone-premise resolution has nothing to resolve against) — found
necessary because the real failing benchmark had an intervening `not_not` axiom fact already
folded into a single-premise `th_resolution` by an earlier pass, with *that* step (not the
originally-trivial one) feeding the `tautology` step; `used_as_taut_premise` alone only catches a
clause's *direct* `TautAST` consumers, not this one-hop-removed case.

**Impact:** fixes the crash for both `get_clause` representative benchmarks (`get_clause/01`,
`/02`) — neither crashes anymore. Verified zero regressions against the full 439-file
`examples/regress` suite plus all 8 sanity tests.

**Known remaining limitation (both `get_clause` benchmarks, undiagnosed further):** once the crash
is fixed, both files run to completion but return `false`. Traced (via `Verit_Checker_Trace`, the
same "first appearance of literal `0` in any computed value" methodology established earlier in
this document) to a *separate*, pre-existing bug: both files have a `th_resolution` step folding
one genuinely useful premise together with `not_simplify`/`tautology`-derived premises that share
no resolution pivot with *anything* (in the concrete case: `th_resolution :premises (t8 t9 t13)`
where `t8` alone already equals the step's declared conclusion, but `t9` — a self-identity
equality — and `t13` — literally the constant `true`, i.e. `Lit._true`, the same reserved literal
`0` used elsewhere as the checker's give-up sentinel, confirmed via `Var._true := 0` in
`src/State.v` — contribute nothing). `State.v`'s `C.resolve` is a strict, sequential, sorted-merge
fold (`S.set_resolve`'s `foldi`) that, when a fold step's "held" pivot literal can't find its
complement before the other side's list runs out, silently *discards* it rather than preserving it
(traced through `resolve`/`resolve_aux`'s `Gt`-case specifically) — so `t8`'s genuinely useful
content gets dropped once it's folded against `t9`/`t13`'s vacuous ones, and the step ends up
proving only `True` instead of its declared conclusion. This is a real mismatch between veriT's
own (apparently more tolerant of redundant premises) `th_resolution` semantics and SmtCoq's strict
fold, and reappeared independently in the `get_eq` investigation below (`get_eq/01`, `/02`, and
`/03` all hit the same thing, once the separate `process_trivial` bugs documented in fix 5 below
stop masking it) — a general fix would mean changing how `mk_clause` compiles `Reso`/`Threso`
(`src/verit/veritSyntax.ml`, shared by every proof rule) and needs a soundly-designed strategy for
recognizing and skipping vacuous premises without silently dropping genuinely-needed ones; left
for a future session rather than attempted under this session's time budget.

### 2. `process_trivial`'s `weakened_ids` incorrectly threaded across unrelated eliminations

**Bug:** `weakened_ids` (accumulated within `process_trivial_aux`/`process_tl`) exists to stop a
single elimination's cascade from re-patching the same downstream step twice if it's reachable via
multiple paths within *that one* trivial-clause's own patching walk. But the code threads the same
accumulated set into the *next*, entirely unrelated top-level elimination
(`process_trivial_aux acc tl' cog weakened_ids'`, carrying `weakened_ids'` forward instead of
resetting it) — so once some step `S` has been patched once (for trivial clause `A`), it's
permanently marked "already weakened" and silently skipped by every *later* elimination too, even
when `S` genuinely depends on a second, different trivial clause `B` that also needs to be patched
out of `S`'s premise list. Found via a real proof where a 4-premise `Reso` step depended on two
independently-trivial clauses; patching it for the first left it permanently marked, so the second
patch was silently skipped, leaving `S` citing the second clause's id after that clause was
dropped — `get_clause: clause number ... not found`.

**Fix:** `weakened_ids` is now reset to `[]` when starting the *next* top-level elimination,
instead of carrying the previous one's forward. It's still threaded correctly *within* one
elimination's own cascade (including the nested "recursive trivial clause" `process_tl` call),
which is the only scope the mechanism was ever meant to cover.

**Impact:** fixes the crash for `get_eq/02` (no longer crashes; still returns `false` — see below).
Verified zero regressions against the full suite.

**A second, related bug found alongside this one:** the "found a recursive trivial clause" branch
of `process_tl` (entered whenever `replace_res` can't find a partner premise for the clause being
eliminated, and heuristically assumes this means the *consumer* step is itself also trivial and
should cascade-eliminate the same way) computed the cascade correctly — patching the consumer's own
downstream references — but then still kept the consumer's own, *unpatched* step (`replaced`, i.e.
`[s]`, unchanged) in the output via `List.rev_append replaced acc`. Since the whole point of this
branch is "this step is being eliminated exactly like the original trivial clause", keeping it
verbatim left it citing the very id that's being dropped one level up. **Fix:** don't re-add
`replaced` — `process_tl acc c1 x notx t' t1i ids_rem res pids weakened_ids''` (drop it, matching
how the original trivial clause itself is dropped by its own caller). Verified zero regressions;
without the `taut_protected` fix above this would have broken `get_clause`'s `tautology`-consuming
case (dropping a step a `tautology` step still needs) — the two fixes' scopes are complementary
(`taut_protected` prevents the *outer* elimination from starting when it would need this, so this
cascade-drop path is only ever reached for genuinely-safe-to-drop cases).

### 5. `process_trivial`'s "recursive trivial clause" cascade could crash or dangle

Two more bugs in the same area, both hit by `get_eq/01` (which used to crash outright).

**Bug A: forcing an elimination that isn't really there.** When a step `i` uses an eliminated
clause `p, ~p` but none of `i`'s *other* premises mention `p` or `~p` either, the code assumes
`p`/`~p` must have survived, uncancelled, into `i`'s own result - so `i`'s own clause should, in
turn, contain some complementary pair of its own, and can be cascade-eliminated the same way:

```
    p, ~p           i's other premises (none with p or ~p)
    -----------------------------------------------------res
                             i : y
```
```
    q, ~q, z           i's own consumers...
    ---------------------------------------res
                  (whatever used i)
```

That assumption isn't always true - `y` can genuinely have no complementary pair, even though
nothing else in `i`'s premises directly cancelled `p`/`~p`. The old code called `find_triv_lits`
on `y` regardless and crashed when it found nothing.

**Fix:** when this happens, give up on eliminating `p, ~p` entirely and leave it (and everything
that depends on it) in the certificate unchanged. This is always safe: `p, ~p` was a valid step
before process_trivial ever touched it, so leaving it alone just skips an optimization rather
than breaking anything.

**Bug B: picking a partner that's also about to disappear.** When `i` *does* have another
premise sharing `p` or `~p`, that premise (call it `t2`) becomes the replacement's own new
premise:

```
    p, ~p         q, ~q, ~p           (t2, itself trivial: has both q and ~q)
    -----------------------------res
               i : q, ~q
```

If `t2` happens to be trivial in its own right, it gets eliminated too, by a separate step of
this same pass - but nothing stopped it from being picked as a partner first, so the new step
built to replace `i` ends up citing an id that's about to be dropped.

**Fix:** exclude any candidate partner that is itself trivial (and not otherwise protected) from
the partner search.

**Impact:** with both fixes, `get_eq/01` no longer crashes. It still returns `false`, but for a
different reason - the same vacuous-premise `th_resolution` issue documented in fix 1 above,
shared with `get_clause/01`, `/02`, and `get_eq/02`/`/03` (a duplicate of `/02`) - not something
process_trivial itself is responsible for. Verified against the full 439-file suite plus all 8
sanity tests, zero regressions.

### `findi`: reversed-premise orientation in `process_cong`'s `and`/`or`-congruence handlers

**Bug:** `process_cong`'s `And`/`Or`-congruence cases assume each premise's equality literal is
always written with a fixed operand order (the "target" side's operand always in a specific
position — second, for the code as originally written). veriT/cvc5 don't guarantee this: a `cong`
step over `and`/`or` can emit a premise as `b = y` instead of `y = b`. The `And`-congruence
handler used `findi` (a linear search assuming the fixed orientation) to locate an argument's
position by value, which raises `Debug "findi: element not found"` when the orientation is
flipped — an outright crash. The `Or`-congruence handler (already restructured earlier this
session for the position-interleaving fix) uses positional `List.nth` instead of `findi`, so the
same root cause doesn't crash it — it silently builds the *wrong* `Equp1AST`/`Equp2AST` axiom
instance instead, a much more insidious failure (checks out step-by-step, wrong final answer).

**Why the equality can't just be reordered:** the natural fix would be to canonicalize the
premise's operand order once, upfront. This is unsound here: for a genuine first-order term
equality, SmtCoq's atom interning canonicalizes direction automatically (`Atom.mk_eq_sym`), but
for a Boolean/`iff`-typed equality (exactly the case for an `and`/`or`-argument congruence
premise), `HashedForm.equal`'s comparison is positional and non-symmetric — rebuilding `Eq (x, y)`
as `Eq (y, x)` produces a genuinely different, non-identical `Fiff` atom that then fails to match
the premise's own clause literal when resolved against it (the same distinction established
earlier this session for `process_same`'s `eq_is_symmetrized` fix).

**Fix:** never reorder the premise's own equality. Instead, detect *which* operand is the
target-side one and choose between `Equp1AST` (`[Not peq; x; Not y]`, the shape when `y` is the
target-side operand, as originally assumed) and `Equp2AST` (`[Not peq; Not x; y]`, when `x` is
instead) accordingly — either axiom's own shape must match `peq`'s true, unchanged operand order
for the checker's fresh-from-`peq` reconstruction to accept it. For `And`-congruence (which used
`findi`), this is factored into a new shared helper, `and_cong_prem_fact`, used by both of the
handler's two symmetric loops. For `Or`-congruence (which uses positional `List.nth`, so the
existing `findi`-based detection doesn't directly apply), the same orientation check is inlined
into both `per_pos1` and `per_pos2` directly, choosing `Equp1AST`/`Equp2AST` based on whether
`get_expr y = get_expr yk` (or the `x`/`xk` symmetric check) holds.

**Impact:** fixes the crash for the hand-minimized `findi/min` reproduction (now `= true`).
Verified zero regressions against the full 439-file suite plus all 8 sanity tests.

**Follow-on fix (`findi/01`, `/02`): duplicate disjuncts in a single `Or`-congruence.** Once the
orientation crash above was fixed, both real-world benchmarks ran to completion but still returned
`false`, due to a *separate* structural issue: genuine duplicate disjuncts within a single
`Or`-congruence's argument list (e.g. `ys` containing the same value at two different positions).
The per-position `OrnAST` projection scheme processes each position independently, consuming
`List.nth xs idx` (`per_pos1`) or `List.nth ys idx` (`per_pos2`) out of the shared unfold
accumulator (`orpi1`/`orpi2`) - but SmtCoq's clauses are sets, not multisets. Once the *first*
occurrence of a shared value is projected away (replaced in the accumulator by the target `Or`),
a *second* position sharing that same value finds nothing left to cancel against - `C.resolve`
tags the fold with its `_true` give-up sentinel there, discarding whatever else the fold still
needed. **Fix:** a new `first_occurrence_mask` helper flags, for a term list, which positions are
the *first* occurrence of their (`get_expr`-normalized) value; `per_pos1`/`per_pos2` now skip
generating any `eqp`/`orn` facts at all for a repeat occurrence, contributing nothing to that
fold - the first occurrence alone already establishes what's needed, so a repeat's own premise
(`pid`) simply goes unused, which is sound (using fewer of the available premises never makes a
derivation unsound, only using one *incorrectly* would). Verified zero regressions.

**Second follow-on fix (`findi/01`): `process_trivial`'s triviality checks were blind to shared
(`STerm`) terms.** With the duplicate-disjunct fix in place, `findi/01` progressed further but
still returned `false`. Traced (via `Verit_Checker_Trace`'s diverge-finder, extended with a
temporary `store_shared_terms` dump to inspect exactly what each `:named` term expanded to) to an
`equiv_pos2` axiom step whose own two named subterms - `@p_39` (`or (not grn_MR) (not (not
prt))`) and `@p_38` (`or (not grn_MR) prt`) - are the *same* formula once double-negation is
collapsed (`not (not prt))` and `prt` share a literal), even though neither name's own top-level
shape reveals this. This makes that step's own declared clause genuinely trivial (contains a
literal and its negation) - but `process_trivial`'s own triviality check
(`neg_mod_dneg_symm`/`eq_mod_dneg_symm`, used in the top-level "is this clause trivial" guard, in
`find_triv_lits`, and in `replace_res`'s partner search) compares raw `term` structure directly,
with no awareness of `STerm` (SmtCoq's reference to a separately-`:named`, shared subterm - see
`get_expr`). Comparing `STerm "p_38"` against `Not (STerm "p_39")` directly falls through to plain
OCaml structural equality (false, different strings) - neither name's *own* shape is a negation of
the other; only their fully-*dereferenced* content is. So the step was never recognized as
trivial, and participated in a downstream 3-premise `Res` fold as a "premise" that's actually a
disguised tautology - `C.resolve`'s single-pivot-per-fold merge found and canceled the accumulator
literal that happened to sort first, never reaching the *other* half of the tautology's own
complementary pair, tainting the fold with `_true` and discarding a premise's genuinely-needed
content - the same "checks out step-by-step, wrong final answer" signature as everywhere else in
this document. **Fix:** `neg_mod_dneg_symm`/`eq_mod_dneg_symm` themselves now dereference both
sides via `get_expr` first, before doing anything else - rather than adding separate
dereferencing wrappers used only at the three sites above, the two comparison functions were
changed directly, since a dedicated `_expr`-suffixed pair turned out to be unnecessary: every one
of `eq_mod_dneg_symm`'s other four call sites (`process_trans`'s reordering fold,
`process_simplify`'s `and`/`or`-collapses-to-`False`/`True` cases) already passes terms that were
dereferenced by their own caller beforehand, so dereferencing again there is a harmless no-op, not
a behavior change. This also fixes a latent gap for free: the two functions' own recursive
sub-term comparisons (`check_arg_lists`, for `And`/`Or`/etc. argument lists) previously compared
raw, non-dereferenced sub-terms even when the top level had been dereferenced by a caller - now
every level dereferences uniformly. The literals *returned*/removed from clauses elsewhere still
use the original, un-dereferenced terms (only the comparison itself dereferences, nothing about
what gets stored in the output certificate changes), so nothing downstream that matches against
the original certificate's own representation is affected. **Impact:** with both fixes, `findi/01`
and `findi/02` now return
`= true`. Verified against the full 439-file suite plus all 8 sanity tests, zero regressions.

### 3. `process_trivial`'s "recursive trivial clause" cascade wasn't tail-recursive

**Bug:** found while checking `trans/02` (a ~24k-line proof) for crashes with the two fixes above
applied — it compiled far longer than its size alone would suggest, then failed outright with
OCaml's `Error: Stack overflow.` (not a `Debug` exception - a genuine unbounded-looking native
stack blowup, the same failure mode documented earlier in this file for `process_cong`/
`process_trans`/etc. before their own tail-recursion fixes). Confirmed *not* pre-existing: the
unmodified baseline, given the same 900-second budget, neither crashed nor finished (it's simply a
slow file to begin with — see below) - so the crash was new. Confirmed *not* an infinite loop
either: re-run with the OS stack-size limit raised from the default 8MB to 1GB, it again neither
crashed nor finished within 900 seconds - consistent with a large but genuinely *bounded* recursion
depth, not runaway recursion.

**Root cause:** the "found a recursive trivial clause" branch of `process_tl` (`process_trivial`'s
inner per-elimination loop) makes a **non-tail** nested call to `process_tl` itself whenever the
step it's patching (`t3`) turns out to also need cascading elimination - it must fully resolve
that nested call (patching all of `t3`'s own downstream consumers, exactly as fix 2 above patches
this) *before* it can resume scanning for its own remaining targets, so the `let t', ... =
process_tl ... in process_tl ...` pattern keeps one native OCaml stack frame alive per level of
cascading. This was always non-tail-recursive, but the *previous* `weakened_ids` and
dangling-reference bugs (fixes 2 and its sibling above) meant many such cascades were silently
skipped or only partially processed rather than actually recursing to completion - once those bugs
were fixed and cascades started running *correctly*, a real proof with a long enough chain of
trivial clauses each depending on the next made this latent non-tail-recursion bite for the first
time. In other words: this session's own correctness fixes made *more*, previously-suppressed
recursion actually happen, and it happened to be deep enough here to overflow the stack.

**Fix:** rewrote `process_tl` as `process_tl_iter`, converting the implicit call-stack recursion
into an explicit task stack - since every level of cascading scans forward over the exact same
underlying certificate remainder (a nested call always continues from right where its caller left
off, and always fully drains before the caller resumes), the whole thing is really just one
forward walk that pushes a new task frame `([], c3, x3, notx3, t3, ids', new_res, new_pids)`
whenever a recursive trivial clause is found, and pops back to the enclosing task once the
innermost one's own `ids` (or the certificate itself) runs out - matching the same
accumulator-based tail-recursion pattern used throughout this file's earlier stack-overflow fixes,
just applied to an explicit stack of pending searches instead of a flat accumulator, since each
task carries its own pivot literals (`c1`/`x`/`notx`) and target id (`t1i`) alongside its own
accumulator.

**Impact:** `trans/02` no longer stack-overflows - re-run with the fix and the *default* 8MB stack,
it ran the full 900-second budget without crashing (matching the unmodified baseline's own
behavior under the same budget - see below for why it still doesn't finish in that time). Verified
zero regressions against the full 439-file `examples/regress` suite (re-run after this fix,
439/439) plus all 8 sanity tests.

### 4. `process_cong`'s congruence handlers folding the same underlying value more than once

**Bug (`subproof/01`):** already fixed as an incidental side effect of an earlier fix in this
session (most likely the `STerm`-dereferencing fix in `neg_mod_dneg_symm`/`eq_mod_dneg_symm`,
given `process_trivial` is on the path everything else feeds through) - confirmed by re-running it
directly (`= true`) with no further change needed. Not independently diagnosed further, since it
was already passing by the time this category was investigated.

**Bug (`subproof/02`):** returned `false`. Traced (via the same `Verit_Checker_Trace`
diverge-finder methodology, with a fix to the parsing script itself - a `WARNING: assuming the
following hypothesis` message can get interleaved mid-line with the trace's own output when both
land on the same file descriptor, breaking a naive line-based regex) to *two* separate instances
of the same underlying problem, both in `process_cong`, both variants of a pattern already fixed
once this session for `Or`-congruence's duplicate disjuncts (see `findi`'s write-up above) but not
yet applied to these other two call sites:

- **Same premise id, cited twice.** `process_cong`'s generic (non-`and`/`or`) congruence case -
  used for a `cong` step over an arbitrary function or predicate, building one `EqcoAST`/`EqcpAST`
  axiom fact plus a flat `Res` over all the premises - assumed every explicit premise contributes
  a genuinely distinct pivot. veriT/cvc5 don't guarantee this: found via a real `cong` step whose
  raw premise list was literally `(t51 t51)` - the *same* premise id, used for two different
  argument positions of a binary operator, because both positions happen to share the same
  underlying equality fact (e.g. proving `f(x, x) = f(a, a)` from a single `x = a`). The axiom
  fact's own declared clause can harmlessly list `Not peq` twice (SmtCoq dedups it to one literal
  once interned), but folding the *same premise's clause* into the outer `Res` twice is not
  harmless - the second fold finds nothing left in the accumulator to cancel against (the first
  fold already consumed it), tainting the result with `C._true` and discarding the real
  conclusion - the same failure mode documented repeatedly throughout this file.
- **Different premise ids, same underlying value.** The *And*-congruence handler
  (`resi1s`/`resi2s`, built via the `and_cong_prem_fact` helper) has the exact same vulnerability
  as `Or`-congruence's `per_pos1`/`per_pos2` (each position consumes its own `xk`/`yk` positively
  out of a shared `andn`-unfold accumulator - a set, not a multiset) but never received the
  `first_occurrence_mask`-based fix applied there earlier this session. Found via a real 25-ary
  `and`-congruence where several distinct premises (different ids, several separate `hole`-
  admitted `TRUST_THEORY_REWRITE` facts) each independently proved a different repeated subterm
  equal to `true` - four of the twenty-five positions ended up asserting the *same* value.

**Fix:** a new `dedup_prem_ids` helper (keeps only the first premise id for each distinct equality
value, comparing via the already-`get_expr`-dereferencing `eq_mod_dneg_symm`) replaces the flat
premise list in the generic congruence case. `resi1s`/`resi2s` gained the same
`first_occurrence_mask`-based skip already used by `per_pos1`/`per_pos2`, keyed on `xs`/`ys`
respectively (matching which side each one's own accumulator unfolds). Both fixes are narrowly
scoped to the flat, non-positional premise lists (`pids`, `resi1s`, `resi2s`) - `ptuples` itself is
left untouched everywhere, since `per_pos1`/`per_pos2`'s own indexing into it positionally would
break if it were shortened.

**Impact:** `subproof/02` now returns `= true`. Verified against the full 439-file suite plus all
8 sanity tests, zero regressions.

### `cong`, `trans`: a note on sheer file size

`cong/01` (a ~10k-line proof) no longer crashes with this session's fixes applied. `cong/02` and
`trans/01` (~75k and ~84k lines respectively) are large enough that `coqc` takes many minutes;
`cong/02` was confirmed to take over 400 seconds on *both* the fixed and the unmodified baseline
code (identical `timeout`-elapsed behavior either way, neither crashing nor finishing) — its
slowness is pre-existing and unrelated to anything changed this session, not a regression, and
wasn't fully checked to completion within this session's time budget; the same is true of
`trans/02` itself even after its stack-overflow fix above - both it and the unmodified baseline
need well over 900 seconds to actually finish. This class of large, genuinely slow files is a
separate, pre-existing performance characteristic (matching this document's own earlier
observation, from session 1, that most of the currently-shipped `sledgehammer-benchmarks` corpus
is comparatively short and doesn't exercise this) - not something addressed this session.

### Final state (session 3)

```
examples/regress:                       439 total, 439 True/OK, 0 False, 0 Error, 0 Timeout
examples/aletheTests/sanitychecktests:  test1-8 (cvc5 + veriT where applicable) all = true
```

Seven general `process_trivial` bugs fixed (`taut_protected`; the `weakened_ids` cross-elimination
scoping bug; the "recursive trivial clause" branch's dangling-reference bug; that same branch's
non-tail-recursion, rewritten as `process_tl_iter`'s explicit task stack; its `STerm`-blind
triviality checks, fixed by making `neg_mod_dneg_symm`/`eq_mod_dneg_symm` dereference their own
arguments via `get_expr`; the same cascade forcing an elimination onto a step that genuinely
isn't trivial, now given up on instead of crashed on; and `replace_res`'s partner search being
able to pick a partner that's itself about to be eliminated) plus four `process_cong` bugs
(reversed-premise orientation in `and`/`or`-congruence, via `and_cong_prem_fact` and the
`per_pos1`/`per_pos2` orientation checks; duplicate disjuncts within a single `Or`-congruence, via
`first_occurrence_mask`; the same duplicate-value vulnerability in `And`-congruence's
`resi1s`/`resi2s`, via the same helper; and a premise id cited twice in the generic
congruence-over-functions/predicates case, via the new `dedup_prem_ids`) — all eleven verified
against the full suite with zero regressions. Every one of the `get_clause`, `get_eq`, `findi`,
and `subproof` categories' crashes is fixed for its representative benchmarks, and `findi` and
`subproof`'s representative benchmarks now fully pass (`= true`); several benchmarks in the other
categories (and the untouched `cong`/`trans` categories' large files) have separate, deeper,
documented-but-unfixed `false`-result or sheer-file-size performance limitations that a future
session can pick up using the same `Verit_Checker_Trace` diverge-finder methodology used
throughout this document.

**Per-file status, `examples/aletheTests/QFUFTests`:**

| File | Status | Issue (if failing) |
|---|---|---|
| `findi/min/min.v` | Passes (`= true`) | — (hand-minimized repro for the orientation fix) |
| `findi/01` | Passes (`= true`) | Fixed: orientation crash, duplicate-disjunct fold, and `process_trivial`'s `STerm`-blind triviality check (see `neg_mod_dneg_symm`/`eq_mod_dneg_symm`) |
| `findi/02` | Passes (`= true`) | Fixed by the same three fixes as `/01` |
| `get_clause/01` | Runs, `= false` | Crash fixed (`taut_protected`). Remaining: `th_resolution` folding one useful premise with vacuous `not_simplify`/`tautology` ones that share no pivot — `C.resolve`'s strict fold silently discards the useful content |
| `get_clause/02` | Runs, `= false` | Same fix, same remaining issue as `/01` (confirmed via trace — identical shape) |
| `get_eq/01` | Runs, `= false` | Crash fixed (fix 5: give up gracefully instead of forcing an elimination, and don't pick a partner that's itself about to be eliminated). Remaining: same vacuous-premise `th_resolution` family as `get_clause` |
| `get_eq/02` | Runs, `= false` | Crash fixed (`weakened_ids` scoping fix). Remaining: same vacuous-premise `th_resolution` family as `get_clause` |
| `get_eq/03` | Runs, `= false` | Identical file to `/02` — same status |
| `subproof/01` | Passes (`= true`) | Fixed incidentally by an earlier session fix (likely `neg_mod_dneg_symm`'s `STerm`-dereferencing) |
| `subproof/02` | Passes (`= true`) | Fixed: two `process_cong` duplicate-value bugs (`dedup_prem_ids`, and `first_occurrence_mask` applied to `And`-congruence) |
| `cong/01` | Runs, `= false` | No longer crashes (benefits from the same `process_trivial`/`process_cong` fixes). Root cause of the `false` not diagnosed — ran out of time |
| `cong/02` | Not fully checked | ~75k-line proof; times out (400s+) on *both* fixed and baseline code — pre-existing slowness, not a regression, but never ran to completion this session |
| `trans/01` | Not actually tested | Never run to a real conclusion this session — a stray leftover process for it turned up mid-session and was killed without knowing its outcome |
| `trans/02` | Crash fixed, verdict unknown | Was stack-overflowing; fixed via the `process_tl_iter` tail-recursion rewrite. Confirmed no longer crashes (ran 900s clean under the default stack), but never finished compiling in the time given, so whether it ends in `true` or `false` is unknown |

Caveats: the "presumed same family" call for `get_eq/03` is inferred from file similarity, not
independently traced the way `get_clause`'s two files were (`findi/02` no longer needs this
caveat - it was independently re-run and confirmed `= true` after the `findi` fixes above) - and
`trans/01` genuinely wasn't verified at all.
