No exceptions are raised, but checker fails.

Proof File: x2020_08_03_15_24_41_942_6515590.cvc5oldpf
SMT File: x2020_08_03_15_24_41_942_6515590.smt_in
Path: /home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-cvc5-old/Benchmarks/isabelle-mirabelle/BO_cvc42

Problem1: DSL was producing an eq_simp that we don't support, due to our eval hack. 

Fix: Just added support to this form of eq_simp. In the future we should probably elaborate this away by verit2016.

Problem2: Returned a not well-typed error until all_simplify's symmetric equality case was fixed. See #26 for the minimal problem. Seems like congruence of `not` over the symmetric `all_simplify` creates this issue. For example:
```
-----------------all_simplify
(x = y) = (y = x)
-------------------cong
!(x = y) = !(y = x)
```

Fix:
