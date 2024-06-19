# First Problem

Initial exception was raised for subproof with multiple assumptions:
```
Message: | VeritAst.preprocess_certif: failed to preprocess || process_subproof: expecting the last step of the certificate to be a discharge step at id t7 |
Position: Line 46 Position 1
```

Proof File: x2020_07_23_15_39_12_904_5134392.cvc5pf
SMT File: x2020_07_23_15_39_12_904_5134392.smt_in
Path: /home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks/Benchmarks/isabelle-mirabelle/HOL-Library/smt_verit/

Additionally, the same problem arose for:
Proof File: x2020_07_24_02_11_33_512_5107654.cvc5pf
SMT File: x2020_07_24_02_11_33_512_5107654.smt_in
Path: /home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks/Benchmarks/isabelle-mirabelle/HOL-Library/smt_verit/

Proof File: x2020_07_28_22_37_31_677_6064540.cvc5pf
SMT File: x2020_07_28_22_37_31_677_6064540.smt_in
Path: /home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks/Benchmarks/Ordered_Resolution_Prover_veriT/

Problem:
Rules that project from premises (like `not_or`) that are located inside subproofs access premises from 
before the subproof.

Fix: Correct the recursive call to `process_proj` for subproofs so that they can look in the outer proof. Fixed!

Now the problem returns a NotWellTyped exception.

# Second Problem
Another fix was that we realized `process_same` needs to be the last transformation. However,
doing this brings about a different problem in x2020_07_23_15_39_12_904_5134392.cvc5pf.
`process_same` handles `symmetry` and `contraction`. 
Contraction needs to come at the end because it (`process_same`) removes clauses that the Coq checker will
consider same, but the other transformations don't. For example, if clause c1 contains 
duplicates, and c2 is c1 modulo duplicate removal, c2 is the "same" as c1 for the checker
since it reasons modulo duplicate removal, but `process_same` would remove c2 and some c3 that
points to c2 would now point to c1; other transformations here don't reason modulo 
duplicate removal, so they would see the duplicate in c1, when they would be expecting
to have the duplicates removed.
Symmetry needs to come before transitivity (this is a guess) because transitivity needs the 
order to be fixed. However, our transitivity should work modulo symmetry, so we need to make
sure that this is the case.

Fix: Make sure transitivity works modulo symmetry.