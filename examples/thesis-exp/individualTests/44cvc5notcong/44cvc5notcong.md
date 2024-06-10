Checker fails.

Proof File: x2020_07_24_09_08_53_363_5071014.cvc5pf
SMT File: x2020_07_24_09_08_53_363_5071014.smt_in
Path: /home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks/Benchmarks/isabelle-mirabelle/HOL-Library/smt_verit

Problem: Returned a not well-typed error until all_simplify's symmetric equality case was fixed. See #26 for the minimal problem. Seems like congruence of `not` over the symmetric `all_simplify` creates this issue. For example:
```
-----------------all_simplify
(x = y) = (y = x)
-------------------cong
!(x = y) = !(y = x)
```

Fix:
