# Checker for `ac_simp`

`ac_simp` is a tautological rule (a rule that takes no premises) in the Alethe proof format. It reduces arbitrary and/or chains in 2 ways:
1. Flatten applications (ex: `a v (b v c) = a v b v c`)
2. Remove duplicates (ex: `a ^ b ^ b = a ^ b`)

The `Flatten` rule in SMTCOQ takes two formulas as input and checks that they are equivalent, in particular up to flattening. Its checker is in `Syntactic.v` (see `check_flatten_body`).
It remains to be confirmed whether it removes duplicates.

## Approach 1 (Unfeasible)
Since `ImmFlatten` (the SmtCertif version of `Flatten`) is a premise-conclusion rule and `ac_simp` is a tautological
rule proving equivalence `x = y`, this approach 
tries to create a new clause that derives `x` 
using `mkRootV` and then derive `y` from `x` using `ImmFlatten`.

*Problem:* Roots are only for initial assumptions and they can't be used to insert 
arbitrary steps into the certificate.

## Approach 2 (Unfeasible)
Given `x = y` proven by `ac_simp`, introduce two subproofs:
```
--assume
x
--ImmFlatten
y

--assume
y
--ImmFlatten
x
```
and then process them using `process_subproof`.

*Problem:* `ImmFlatten` is a premise-conclusion rule, and `process_subproof` will fail on it because it expects all rules to be tautological. For example:
```
Certif after process_subproof: 
(h1, AssumeAST, (cl  ((not ((and  a (and  b c)) = (and  a b c))))), [], [])
(x7, Equn1AST, (cl  (((and  a (and  b c)) = (and  a b c))) ((not (and  a (and  b c)))) ((not (and  a b c)))), [], [])
(x5, AndnAST, (cl  ((and  (and  a (and  b c)) (not (and  a b c)))) ((not (and  a (and  b c)))) ((and  a b c))), [], [])
(x9, ResoAST, (cl  ((and  (and  a (and  b c)) (not (and  a b c)))) (((and  a (and  b c)) = (and  a b c))) ((not (and  a (and  b c))))), [ x5 x7], [])
(x8, Equn2AST, (cl  (((and  a (and  b c)) = (and  a b c))) ((and  a (and  b c))) ((and  a b c))), [], [])
(x6, AndnAST, (cl  ((and  (and  a b c) (not (and  a (and  b c))))) ((not (and  a b c))) ((and  a (and  b c)))), [], [])
(x10, ResoAST, (cl  ((and  (and  a b c) (not (and  a (and  b c))))) (((and  a (and  b c)) = (and  a b c))) ((and  a (and  b c)))), [ x6 x8], [])
(t2, ResoAST, (cl  ((and  (and  a (and  b c)) (not (and  a b c)))) ((and  (and  a b c) (not (and  a (and  b c))))) (((and  a (and  b c)) = (and  a b c)))), [ x9 x10], [])
(t3, ResoAST, (cl  ((and  (and  a (and  b c)) (not (and  a b c)))) ((and  (and  a b c) (not (and  a (and  b c)))))), [ h1 t2], [])
(x14, AndpAST, (cl  ((not (and  (and  a b c) (not (and  a (and  b c)))))) ((and  a b c))), [], [ 0])
(x13, ResoAST, (cl  ((and  (and  a (and  b c)) (not (and  a b c)))) ((and  a b c))), [ t3 x14], [])
(x4, AcsimpAST, (cl  ((and  a (and  b c)))), [ x13], [])
(x15, AndpAST, (cl  ((not (and  (and  a b c) (not (and  a (and  b c)))))) ((not (and  a (and  b c))))), [], [ 1])
(x16, ResoAST, (cl  ((and  (and  a (and  b c)) (not (and  a b c)))) ((not (and  a (and  b c))))), [ t3 x15], [])
(x17, ResoAST, (cl  ((and  (and  a (and  b c)) (not (and  a b c))))), [ x4 x16], [])
(x19, AndpAST, (cl  ((not (and  (and  a (and  b c)) (not (and  a b c))))) ((and  a (and  b c)))), [], [ 0])
(x18, ResoAST, (cl  ((and  a (and  b c)))), [ x17 x19], [])
(x3, AcsimpAST, (cl  ((and  a b c))), [ x18], [])
(x20, AndpAST, (cl  ((not (and  (and  a (and  b c)) (not (and  a b c))))) ((not (and  a b c)))), [], [ 1])
(x21, ResoAST, (cl  ((not (and  a b c)))), [ x17 x20], [])
(x22, ResoAST, (cl ), [ x3 x21], [])
```
Here, we expect `x13` and `x4` to represent:
```
and a b c
---------------------ImmFlatten
and a (and b c)
```
but instead we have:
```
((and  (and  a (and  b c)) (not (and  a b c)))) ((and  a b c)))
-------------------------------------------------------------------------------ImmFlatten
and a (and b c)
```

## Approach 3
### Task: Add `Flatten` - the non `Imm` version of `ImmFlatten` to `SmtCertif`. 
Use the Coq code that already exists for
the checker for `ImmFlatten` in SMTCoq. It should be 
reusable. Now `ac_simp` simply reduces to `Flatten`.

***Done***
This works for flattening! Note that it doesn't work if the literals in the or/and are reordered, but this 
should be okay. For example: `ac_simp` can't prove `(= (or a b c) (or (or b a) c))` but it can prove
`(= (or a b c) (or (or a b) c))`.

### Task:  Prove `Flatten` correct

### Task: Add duplicate removal
`ac_simp` doesn't work for duplicate removal. This needs to be added to the checker. From `examples/aletheTests/testrewrites/`, `acsimp.
v` and `acsimp2.v` are successful tests for flattening in
by `ac_simp` and `acsimp3.v` is a failed test showing that duplicate removal doesn't work.

***Done***
From `examples/aletheTests/testrewrites/`, tests `acsimp.v` through `acsimp4.v` all pass. We needed to thread duplicate removal through 
with flattening.

### Task: Add and/or removal
`ac_simp` currently isn't reducing singleton `and` and `or` terms. For example, it's okay with `(= (and c c) (and c))` in `acsimp6`
but fails with `(= (and c c) c)` in `acsimp7`. Fix this case as well. This should also fix `acsimp5` which is just a slightly 
non-trivial case.