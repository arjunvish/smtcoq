# Alethe Task List

This branch of SMTCoq builds a checker for proofs in the Alethe proof format. This is done by
transforming Alethe proof certificates into certificates in SMTCoq's internal proof format. 

The checker is operational but incomplete. It works for a subset of the `QF_UF` logic. It has 
been tested on a set of benchmarks, reduced to the logic that it supports - 
see `/examples/thesis-exp` and [this](https://cs.union.edu/~viswanaa/thesis.pdf) thesis.

## Task List 

### Benchmark Completeness
1. **Make checker complete over thesis benchmarks.** For my thesis I used 138 benchmarks from 
a larger set of (around 4000) benchmarks to compare SMTCoq's alethe checker with its old checker.
It proved more benchmarks and generated less holes, but the new checker still fails (for cvc5) 
on 7 benchmarks. Goal: fix these. All 7 tests are in
[this](https://github.com/arjunvish/smtcoq/tree/alethe_coq8.13/examples/aletheTests/thesisTests) folder. The issue with all tests seem to be 
that the transformations are adding terms to the
clauses in the certificate such that the final 
value doesn't derive the empty clause.
2. **Make checker complete over all sanity check benchmarks.** There are 8 very simple "sanity check" benchmarks for which we expect the checker to work but the checker fails on 4 of these (4/16 because all
8 of them are tested over cvc5 and veriT proofs). 
[This](https://github.com/arjunvish/smtcoq/blob/alethe_coq8.13/examples/aletheTests/sanitychecktests/Notes.md) document explains these benchmark and its 
folder contains all of them. 
3. **Make checker complete over QF_UF benchmarks.** We ran a much larger set of benchmarks on a computing cluster. We filtered the SMTLIB QF_UF benchmark set down to 4115 SMT files and checked each of them against the Alethe proofs produced for them from cvc5 and veriT. That gave 
8230 benchmarks to run the checker over and the results aren't encouraging. The checker returns true for 39, false
for 13, times out for 710 and fails with some sort of exception on 7466 files. The results are explained in the
last page [here](https://docs.google.com/document/d/1hMCaCjCyOfbsnFupOBUtsie-Ane5TCrdwjdbFnaCQzM/edit?usp=sharing).
We need to bring this benchmark set to completion if we want to publish this work. The output from Coq for each of 
these benchmarks is in [this](https://github.com/arjunvish/smtcoq/blob/alethe_coq8.13/examples/aletheTests/QFUFTests/other_v.txt) file.


### Other Issues
1. The checker doesn't support the `ac_simp` rule. This is the main rule that we need to 
support before we go from working on a subset of `QF_UF` to all of `QF_UF`. We'll need to 
figure out a way check rules of type `ac_simp` either by soundly converting them to other rules 
that SMTCoq supports or by extending its checker to support `ac_simp`.
There is a partial implementation in [this](https://github.com/arjunvish/smtcoq/tree/acsimp) branch which is
documented in [this](https://github.com/arjunvish/smtcoq/blob/acsimp/ACSIMP.md) file.
A solution from notes:
  To implement a transformation for `ac_simp`:
    - Add the non-Imm version of `Flatten` to SMTCoq, with duplicate removal, and restrict it to Ands and Ors.
    - Encode `ac_simp` using `Flatten`. Account for duplicates.
2. Fully support `QF_LIA`. Currently, we are able to take the Alethe LIA rules and simply 
pass them to the Micromega checker in Coq. Issues arise when there are rewrites that have
LIA and EUF mixed because Micromega can only work with pure LIA rules. For example, it 
can easily prove `1 = 1` but it can't prove `2 > 1 = true` because it sees a mixed logic.
3. A checker for the `tautology` rule was added and seems to work.
    - Prove the `tautology` checker correct
4. Update this branch to coq8.17. It currently runs coq8.13. Most of this port is done and
resides in the [veritAstBackup](https://github.com/arjunvish/smtcoq/tree/veritAstBackup) branch,
but it has some issues. Specifically, `make` wasn't installing the plug-in fully. I needed to 
run `make install` to have it work. Investigate, fix, run all the tests and once we're sure
that the port is sound, move all the changes from the last few commits to that branch 
(these commits only consists of added documentation and organizing of tests) and start using
that one (this should become back up and that should have a better name, maybe `alethe`).
5. For the subset of `QF_UF` that the checker supports, it currently shows that it's support 
for cvc5 through alethe is "better" than its previous support for cvc4 (thesis benchmarks). 
This is because it leaves a lesser number of holes over the same benchmarks. 
However, there are still many holes, and we want to get to 0 holes. Possible solutions:
    - Can we use veriT-old to elaborate all 44 holes?