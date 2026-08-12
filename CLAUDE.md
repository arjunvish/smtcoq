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
