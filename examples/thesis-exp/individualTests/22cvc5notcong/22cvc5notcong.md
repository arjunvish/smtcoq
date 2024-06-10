No exceptions are raised, but checker fails.

Proof File: x2020_07_29_02_17_01_007_5595370.cvc5oldpf
SMT File: x2020_07_29_02_17_01_007_5595370.smt_in
Path: /home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-cvc5-old/Benchmarks/Ordered_Resolution_Prover_veriT

Problem: Returned a not well-typed error until all_simplify's symmetric equality case was fixed. See #26 for the minimal problem. Seems like congruence of `not` over the symmetric `all_simplify` creates this issue. For example:
```
-----------------all_simplify
(x = y) = (y = x)
-------------------cong
!(x = y) = !(y = x)
```

Fix:
