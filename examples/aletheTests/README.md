# Folder Description

This folder contains many test files for SMTCoq's alethe checker. These are pairs of SMT 
(`.smt2`) files and proof (`.pf`) files. They were generated over time to test different
features of the checker (translator rather). The names of the folders are descriptive enough
but here's a rundown:
- `sanitychecktests` contains 8 simple test file pairs, most of which were manually generated.
These are tests which we expect to hold at the very least. Surprisingly, not all of them do
pass currently. There is more descriptive documentation inside.
- `testcong` and `testrewrites` contain tests for the `cong` rule for Congruence and rewrites 
rules (especially cvc5). These are the two rules that contain most variations.
- `misctests` contains miscellaneous tests and `oldTests` contains some tests that might not
be relevant anymore.

Over the years, I've collected many different sets of benchmarks to test the checker on. These
are too large to reside on Github. They have been zipped up and stored in Google drive. You can 
find these (with a description) [here](https://drive.google.com/file/d/19PNYb8OEVnHzeGbZPRqAM0wkcxy1W3vh/view?usp=sharing). A subset of them have found their way to `thesis-exp` which has a separate description.

The following tests from this directory currently fail
- testcong/testp.v
- testcong/conglt.v
- testrewrites/coq/testeqsimp11.v
