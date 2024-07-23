# Motivation 
Our initial experiments on the Coq List library involved 
finding locations to test the abduce tactic on. This 
was done by stepping through each proof in the entire file, 
keeping track of 1. the current local context, 2. the 
current goal, 3. the next step in the proof, and 
figuring out whether the next step is abducable by the 
SMT solver. It was almost always the case that the next
step in all these test sties was an application of 
either the Coq `rewrite` tactic or its `apply` tactic.
Here, we generalize this observation. 

We rerun the experiments on the List library and the 
`abduce` tactic: we try the `abduce` tactic at 
every location in `List.v` where either the `rewrite`
or `apply` tactic is used.

Experiment Specs:
- Using a copy of `List.v` from `coq-8.13`
- Use latest version of `cvc5` (`1.1.2`)
- Use `smtcoq\smtcoq` version `coq-8.13`
- Replace `rewrite`/`apply` by 
`Fail Timeout 20 (time abduce 1).` and classify into:
1. `abuce` doesn't work, and why it doesn't
2. `abduce` works, get max number of abducts in 20 seconds. 
- Add tags in comments:
    ```
    GOAL #N:
    OUTPUT #N:
    RESULT #N: Success|Failure|N/A|Partial
    ```
    where a result is a 
    * `Success` if an abduct returned by cvc5 is findable 
      in the current (global) context via the `Search` 
      command.
    * `Failure` if the `abduce` tactic works, but isn't 
      able to find a useful abduct.
    * `Smt Success` if an smt solver works in solving a goal. Usually 
      these goals work when `verit` is called (`smt` fails) but the tactic
      leaves behind some `CompDec` goals which is expected.
    * `N/A` if the `abduce` tactic doesn't work on the      
      goal. This can be due to many reasons, the 
      possibilities are recorded below.
    * `Partial` if an abduct returned by cvc5 is in some way
      obvious or findable for the user but not in the same
      way as we evaluate successes with. For example, abduct
      might not be automatable the way we're trying to 
      automate other successes.

Files:
- `List-rewrite.v` contains the results from the 
experiments on the `rewrite tactic.
- `List-apply.v` contians the results from the 
experiments on the `apply` tactic.
- `List-rewrite-chatgpt.v` contains the results from 
the experiments on the `rewrite` tactic using ChatGPT.
- `List-apply-chatgpt.v` contains the results from 
the experiments on the `apply` tactic using ChatGPT.

Misc:
- I add a special tag `(* MARKED: *)` when I want to come 
back to the problem for some reason.
- After SMTCoq is imported, the file doesn't compile. 2 
things need to be changed: in lemmas 
`removelast_firstn_len` and `repeat_eq_cons`, the `pred` 
must be changed to a `Nat.pred`
- To find and comment out all calls to abduce:
Find: `\*\) Fail Timeout 20 \(time abduce ([0-9]*)\)\.`
Replace: `*) (* Fail Timeout 20 (time abduce $1). *)`

## `rewrite` Experiments with `abduce`
- `List-rewrite.v` contains the results from the 
experiments on the `rewrite tactic.
- There are 196 occurrunces of `rewrite`. Replace each one with `Fail Timeout 20 (time abduce 1).`
- That gives a total of 238 goals (`rewrite`s), but 
the last goal # is 239 because my stupid ass forgot to count a GOAL #66.

## `apply` Experiments with `abduce`
- `List-apply.v` contians the results from the 
experiments on the `apply` tactic.
- There are 232 occurrences of `apply`. Replace each one with `Fail Timeout 20 (time abduce 1).`
- That gives a total of 241 goal (`apply`s), but the last
goal # is 243: I must have miscounted on the way.

## `rewrite` Experiments with ChatGPT
- `List-rewrite-chatgpt.v` contains the results from 
the experiments on the `rewrite` tactic using ChatGPT.
We copy the proof until the `rewrite` step and ask 
ChatGPT to complete the proof. Our prompt to ChatGPT:
```
Complete the following Coq proof without removing the tactics that are already part of my proof:
```
followed by proof.

Tags:
1. `Unsound.` : The LLM's solution fails to be checked.
2. `Success:` : The LLM is able to give me the rest of the solution.
3. `Incomplete:` : Solution is checkable by Coq, but doesn't finish the proof.

Problems:
- Often, tactic doesn't apply. 
- Sometimes, it uses tactics that are not in the global context.
- I've seen proofs without a `Qed.` in the end.
- For `firstn_skep_rev`, which has a lot of rewrites incrementally, ChatGPT continuously tried either `rewrite rev_involutive. reflexivity.` or just `reflexivity`, both of which were incorrect (I wasn't telling it it was wrong).
- Sometimes, it gives me a proof that is obviously incomplete. Ex GOAL #53:
```
rewrite skipn_all2; auto.
    -
```
- Sometimes it uses the `lia` tactic that is not accessible.
- For Goal #63, ChatGPT's proof is more efficient.

## Types of tags:
1. `Unexpected` : `abduce` succeeds and modifies the goal. We expect it to fail.
2. `Failure. asserts goal.` : fails and can only give us the goal as the abduct
3. `Failure. asserts goal symmetry.` : same as above but gives symmetry of goal (most likely goal is an equality).
4. `Success. smt fails on Nat goal.` : `abduce` succeeds but `smt` fails because of `nat` goal
5. `Success. smt fails on non-bool goal.` : `abduce` succeeds but `smt` fails because of a non-bool goal
6. `Nat predicate.` : can't use SMTCoq because of a `nat` predicate (`N/A`)
7. `Local lemma.` : a local lemma is rewritten, so `smt` might work here (`N/A`)
8. `Quantified.` : can't use SMTCoq because of a quantified formula
9. `Timeout.` : `abduce` times out (`failure`)
10. `Non-bool predicate.` : can't use SMTCoq because of a non-bool predicate (`N/A`)
11. `Out of bounds.`: SMTCoq returns Uncaught exception Invalid_argument("index out of bounds").
12. `Not subtype.`: SMTCoq returns Solver error: (error argument type is not a subtype of the function's argument type.)
13. `Atom not of expected type.`: SMTCoq returns exception "Atom not of expected type".
14. `Rewrite in hyp.`: The rewrite is being applied to a hypothesis.
15. `Deeply nested.`: The rewrite is deeply nested in other tactics and is not straightforward to isolate.
16. `Failure. Unsound abduct.`: The abduct is unsound in the theory.
17. `Drops nat lemma.`: Tactic doesn't send a lemma that might be necessary to prove the goal since its over a nat predicate.
18. `Drops lemma.`: Similar to above, but for a non-bool predicate.
19. `Free sort.`: SMTCoq returns Solver error: (error Parse Error: <stdin>:4.13: Free sort symbols not allowed in QF_SAT )
20. `Couldn't reconstruct.`: SMTCoq returns: Could not reconstruct abduct
21. `Success. smt fails because of dropped abduct.`: We are able to find and assert the abduct but the smt tactic drops it and so fails
22. `Not automatable.`: This won't fit within our automation scheme where we search for the goal and apply any matches.
23. `Print error.`: Coq cannot parse the abduct the way its printed by the tactic.

# Issues

## Unexpected Problem 1
`smt` fails with
```
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.
Bytecode compiler failed, falling back to standard conversion
[bytecode-compiler-failed,bytecode-compiler]
```
but `verit` solves the goal (leaving out only a couple of `CompDec`s).

This happens with rewrite goals #1, #2, #41, #72, #88, #89, #91, #112, #166, #167, #231, #232
and apply goals #11, #38 #230, #234.

For goals #92, #230 `smt` works.

## Unexpected Problem 2
`smt` fails because cvc4 returns a counter-model; the call to `verit` creates an smt file that is `unsat`, but smtcoq fails on veriT's proof file since it doesn't support the `tmp_qnt_tidy` rule.

This happens with rewrite goals #182, #234

## Unexpected Problem 3
`smt` fails because cvc4 returns a counter-model; the call to `verit` creates an smt file that is `unsat`, but smtcoq fails on veriT's proof file, but its hard to tell why, it gives error message:
```
SMTCoq was not able to check the proof certificate.
```
The proof file is very straightforward:
```
1:(input ((not #1:(= op_0 op_1))))
2:(input (#1))
3:(resolution () 1 2)
```
This happens with apply goal #39.

## Out of bounds
SMTCoq returns `Uncaught exception Invalid_argument("index out of bounds").` This is an SMTCoq bug, see and report `indexoutofboundsBugReport.v` to Chantal.

## Not subtype
SMTCoq returns `Solver error: (error argument type is not a subtype of the function's argument type.)`. This is an SMTCoq bug, see `notsubtypeBugReport.v`. When SMTCoq sees applications of higher-order functions, instead of returning an exception to the user saying they aren't supported by the SMT solver, it coerces the function type of the argument to a flat type. Its not clear in what situations this coercion is happening though, we are not able to reproduce this with a smaller example (maybe the quantified hypothesis plays a role as well?).

## Atom not of expected type
SMTCoq returns `exception "Atom not of expected type"`. This is an SMTCoq bug, see `atomnotexptypeBugReport.v`. From terminal, I get message: `Incorrect type: wanted Tindex_2, got Bool`. Terms `true` and `false` of type Bool are parsed into variables of type Bool in the SMT file, not sure if this is what the issue is.

## Free sort
SMTCoq returns `Solver error: (error Parse Error: <stdin>:4.13: Free sort symbols not allowed in QF_SAT ).` The tactic sets the logic to `QF_SAT` and then tries to declare a sort symbol. 
It should be setting the sort to `QF_UF`. This is an SMTCoq bug, see `freesortBugReport.v`.
This seems to happen only when the goal is False. So SMTCoq asserts `not false` and it 
recognizes that it only needs logic `QF_SAT`. When the `cvc4` tactic is called, this happens 
correctly, but when `abduce` is called, it tries to declare a sort for the list types and this
is not allowed in the `QF_SAT` logic which is why the solver throws an error. This is 
surprising because the code that writes the `declare-sort` commands in the SMT script is 
identical in `call_cvc4` (for the `cvc4` tactic) and `call_cvc4_abduce` (for the `abduce` 
tactic).

## Couldn't Reconstruct
SMTCoq returns `Could not reconstruct abduct`. This is just a funny situation, see 
`coulntreconstrBugReport.v`. When the goal is `False` and SMTCoq discards all lemmas (since 
they are not supported), SMTCoq asks cvc5 to find an abduct for `False` with no hypothesis:
```
(set-option :print-success true)
(set-option :produce-assignments true)
(set-logic QF_SAT)
(get-abduct A false)
```
for which cvc5 returns `fail`. Not sure if we want to change anything here.