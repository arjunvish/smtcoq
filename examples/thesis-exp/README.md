# Thesis Tests
This directory contains experiments conduct for my PhD thesis. The benchmarks came originally from Mathias Fleury. Details (from an email forwarded by Haniel):
- 4260 SMT files
- Each file solvable within 12s by either veriT, cvc4, or Z3.
- The folder name indicates the origin of the problems: PNT (Prime_Number_Theorem), BO (Lambda_Free_KBOs), Green (Green Theorem), Zeta (\Zeta(3) is irrational), HOL-Library (extended standard library of Isabelle).
- All of them have logic `AUFLIA` (in the final set of benchmarks we have 3 files with the `la_generic` rule which is really not much coverage from LIA, so after our reduction of the files, we effectively test for `QF_UF`).

We reduced these files to remove proofs over quantifiers, and a couple of rules that we don't support. We did that in 3 steps:
1. We don't support any proofs/rules containing existential quantifiers. So we simply removed all SMT files that contained `exists`. This reduced the number to 1190.
2. Next we removed all files that contained Real types and `forall`. Additionally we removed any files whose veriT proofs contained the following rules:
    - `qnt_cnf` - a rule that normalizes universally quantifier formulas.
    - `sko_forall` - a rule for skolemization of universally quantified formulas
    - `onepoint` - a rule that eliminates quantified variables that can have only one value
    - `qnt_simplify` - a rule that simplifies a universally quantified formula with a constant predicate
    - `bfun_elim` - a rule that simplifies boolean functions (it involves quantifiers)
    - `ac_simp` - a rule that simplifies nested occurrences of `and` and `or` by recursive flattening and duplicate removal
This left us with 141 files.
3. Finally, we removed the 3 files with LIA in them, leaving 138 files.

We ran our experiments on these 138 files and presented them in the thesis. VeriT results are uninteresting, all tests are checkable both with veriT-2016 and alethe. cvc4 vs cvc5 is more interesting:
| Solver | # Benchmarks | # Successes | # Successes with Holes | # Failures | # Holes | # Files with holes |
|--------|--------------|-------------|------------------------|------------|---------|--------------------|
| CVC4 | 138 | 54 | 77 | 7  | 153 | 82 |
| cvc5 | 138 | 84 | 44 | 10 | 66  | 44 |

`cvc5coqcop14` is the file that contains all the test results

Goals:
- Enumerate all holes
- Can we use veriT-old to elaborate all 44 holes?
- All 10 failed checks raise the same exception. To find a solution, find the individual tests and debug.
```
"File "trace/smtTrace.ml", line 311, characters 4-10: Assertion failed."
```
- Support `ac_simp`. A solution from notes:
  To implement a transformation for `ac_simp`:
    1. Add the non-Imm version of `Flatten` to SMTCoq, with duplicate removal, and restrict it to Ands and Ors.
    2. Encode `ac_simp` using `Flatten`. Account for duplicates.
- Support LIA. Run some tests.