No exceptions are raised, but checker fails.

Proof File: x2020_08_03_17_15_27_694_6279318.cvc5oldpf
SMT File: x2020_08_03_17_15_27_694_6279318.smt_in
Path: /home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-cvc5-old/Benchmarks/isabelle-mirabelle/BO_cvc42

Problem: Returned a not well-typed error until all_simplify's symmetric equality case was fixed. See #26 for the minimal problem. Seems like congruence of `not` over the symmetric `all_simplify` creates this issue. For example:
```
-----------------all_simplify
(x = y) = (y = x)
-------------------cong
!(x = y) = !(y = x)
```
The certificate fails at step `x4` added by `process_cong` for the `not` predicate case:
```
Certif after process_subproof: 
(a0, AssumeAST, (cl  ((not ((not ((f ( x)) = a)) = (not (a = (f ( x)))))))), [], [])
(x9, Equn1AST, (cl  ((((f ( x)) = a) = (a = (f ( x))))) ((not ((f ( x)) = a)))), [], [])
(x10, Equn2AST, (cl  ((((f ( x)) = a) = (a = (f ( x))))) (((f ( x)) = a))), [], [])
(t1, ResoAST, (cl  ((((f ( x)) = a) = (a = (f ( x)))))), [ x9 x10], [])
(x1, Equp1AST, (cl  ((not (((f ( x)) = a) = (a = (f ( x)))))) ((not ((f ( x)) = a))) ((a = (f ( x))))), [], [])
(x2, ResoAST, (cl  ((not ((f ( x)) = a))) ((a = (f ( x))))), [ x1 t1], [])
(x3, Equn1AST, (cl  (((not ((f ( x)) = a)) = (not (a = (f ( x)))))) (((f ( x)) = a)) ((a = (f ( x))))), [], [])
(x4, ResoAST, (cl  (((not ((f ( x)) = a)) = (not (a = (f ( x)))))) ((a = (f ( x))))), [ x2 x3], []) (* PROBLEM *)
f x != a, a = f x        (f x != a) = (a != f x), f x = a, a = f x
------------------------------------------------------------------
               (f x != a) = (a != f x), a = f x
(x5, Equp2AST, (cl  ((not (((f ( x)) = a) = (a = (f ( x)))))) ((not (a = (f ( x))))) (((f ( x)) = a))), [], [])
(x6, ResoAST, (cl  ((not (a = (f ( x))))) (((f ( x)) = a))), [ x5 t1], [])
(x7, Equn2AST, (cl  (((not ((f ( x)) = a)) = (not (a = (f ( x)))))) ((not ((f ( x)) = a))) ((not (a = (f ( x)))))), [], [])
(x8, ResoAST, (cl  (((not ((f ( x)) = a)) = (not (a = (f ( x)))))) ((not (a = (f ( x)))))), [ x6 x7], [])
(t2, ResoAST, (cl  (((not ((f ( x)) = a)) = (not (a = (f ( x))))))), [ x4 x8], [])
(t3, ResoAST, (cl ), [ t2 a0], [])
```

Fix:
