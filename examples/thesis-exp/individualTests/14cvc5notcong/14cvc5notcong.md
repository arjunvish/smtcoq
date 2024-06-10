No exceptions are raised, but checker fails.

Proof File: x2020_08_03_15_14_36_388_6025794.cvc5oldpf
SMT File: x2020_08_03_15_14_36_388_6025794.smt_in
Path: /home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-cvc5-old/Benchmarks/isabelle-mirabelle/BO_cvc42

Problem1:
This rule:
```
(step t5 (cl (= (= (arg_d ua_d) sa_d) (= sa_d (arg_d ua_d)))) :rule all_simplify)
```
Isn't justified by the DSL. Its a symmetric rewrite.

Fix1: Just added a transformation to fix it.


Problem2: Returned a not well-typed error until all_simplify's symmetric equality case was fixed. See #26 for the minimal problem. Seems like congruence of `not` over the symmetric `all_simplify` creates this issue. For example:
```
-----------------all_simplify
(x = y) = (y = x)
-------------------cong
!(x = y) = !(y = x)
```

