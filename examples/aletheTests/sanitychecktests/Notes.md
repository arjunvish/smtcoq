
# Sanity Check Tests
We have 8 sanity check tests:
| Test | Formula                                        | logic | veriT Proof | Comments | cvc5 Proof | Comments     | 
|------|------------------------------------------------|-------|-------------|----------|------------|--------------|
|test1 |`~(T ^ ~T)`                                     | Core  | Success      |          | Success    |              |
|test2 |`T v F`                                         | Core  | Success      |          | Success     |              |
|test3 |`forall p, ~(p ^ ~p)`                           | Core  | Success      |          | Success     |              |
|test4 |`forall a b c, (a v b v c) ^ (~a v ~b v ~c) ^ (~a v b) ^ (~b v c) ^ (~c v a)`    | Core  | Success      |          | Success     |              | 
|test5 |`forall p, p v ~p`                              | Core  | Success      |          | Success     |             |
|test6 |`forall (a b : Z) (P : Z -> bool) (f : Z -> Z), ~(f a = b) v (~ P (f a)) v P b`| QF_UFLIA | Success     |          | Failure    | Smtcoq_plugin.SmtForm.Make(Atom).NotWellTyped(_) |
|test7 |`forall (a b : bool) (x y : Z) (ite a (ite b (= (+ (* 2 x) 1) (+ (* 2 y) 1)) (= (+ (* 2 x) 1) (* 2 y))) (ite b (= (* 2 x) (+ (* 2 y) 1)) (= (* 2 x) (* 2 y)))) => (and (=> a b) (=> b a) (= x y))` | QF_UFLIA | Failure      | Fails at step `t64` as a consequence of `flatten_subproof` of subproofs created by a bool_simplify (at step `t2`)  | Failure     | Failure because of step `(t7, HoleAST, (cl  ((((1 + (2 * op_2)) = (1 + (2 * op_3))) = (op_2 = op_3)))), [], [ ARITH_POLY_NORM (((1 + (2 * op_2)) = (1 + (2 * op_3))) = (op_2 = op_3))])`, Micromega cannot solve this |
|test8 |`forall (x y: Z) (f: Z -> Z), y = x + 1 -> f x = f (y - 1)` | QF_UFLIA | Success     |         | Failure    | Smtcoq_plugin.SmtForm.Make(Atom).NotWellTyped(_) |

## Issues:

### Test6cvc5
```
nwt: (op_2 (aka Smt_var_op_3) op_1 (aka Smt_var_op_2))File "./test6cvc5.v", line 23, characters 5-255:
Error:
Verit.import_trace: processing certificate
Error: VeritSyntax.Debug
Message: VeritAst.process_certif: formula Fatom 2 [1] is not well-typed at id x43
Position: Line 38 Position 1
Offending step from certificate:
```
(x43, Equp1AST, (cl  ((not ((op_3 ( op_2)) = (op_3 ( op_2))))) ((op_3 ( op_2))) ((not (op_3 ( op_2))))), [], [])
```
### Test7verit
```
nwt: (+ (* 2 op_3 (aka Smt_var_op_3)) 1)File "./test7verit.v", line 23, characters 5-256:
Error:
Verit.import_trace: processing certificate
Error: VeritSyntax.Debug
Message: VeritAst.process_certif: formula Fatom +2*1*3++1 is not well-typed at id x1
Position: Line 82 Position 1
```
Offending step from certificate:
```
(x1, Equp1AST, (cl  ((not (((2 * op_3) + 1) = (1 + (2 * op_3))))) (((2 * op_3) + 1)) ((not (1 + (2 * op_3))))), [], [])
```

### Test7cvc5
```
nwt: (+ (* 2 op_3 (aka Smt_var_op_3)) 1)File "./test7cvc5.v", line 23, characters 5-255:
Error:
Verit.import_trace: processing certificate
Error: VeritSyntax.Debug
Message: VeritAst.process_certif: formula Fatom +2*1*3++1 is not well-typed at id x1
Position: Line 61 Position 1

```
Offending step from certificate:
```
(x1, Equp1AST, (cl  ((not (((2 * op_3) + 1) = (1 + (2 * op_3))))) (((2 * op_3) + 1)) ((not (1 + (2 * op_3))))), [], [])
```

### Test8verit
```
nwt: (+ op_1 (aka Smt_var_op_1) 1)File "./test8verit.v", line 23, characters 5-256:
Error:
Verit.import_trace: processing certificate
Error: VeritSyntax.Debug
Message: VeritAst.process_certif: formula Fatom 1++1 is not well-typed at id x4
Position: Line 24 Position 1
```
Offending step from certificate:
```
(x4, Equp1AST, (cl  ((not ((op_1 + 1) = (1 + op_1)))) ((op_1 + 1)) ((not (1 + op_1)))), [], [])
```

### Test8cvc5
```
nwt: (+ op_1 (aka Smt_var_op_1) 1)File "./test8cvc5.v", line 23, characters 5-255:
Error:
Verit.import_trace: processing certificate
Error: VeritSyntax.Debug
Message: VeritAst.process_certif: formula Fatom 1++1 is not well-typed at id x1
Position: Line 37 Position 1

```
Offending step from certificate:
```
(x1, Equp1AST, (cl  ((not ((op_1 + 1) = (1 + op_1)))) ((op_1 + 1)) ((not (1 + op_1)))), [], [])
```