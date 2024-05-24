The benchmarks in this directory from the Carcara paper artifact. The `artifact/sample` directory has a representative sample of 5% of the SMTLIB benchmarks 
for the theories in consideration for the paper. This directory contains only the `QF_UF` benchmarks from that sample.
There are 208 `.smt2` files in this benchmark set now (and their corresponding veriT proof files).

Before the initial experiment can be run the following issues have to be fixed:
1. Identifiers have `$` in their name which the SMTCoq parser doesn't allow. Either change the parser to accept it in identifier names (tried briefly but not able to 
    do this) or replace all occurrences of `$` with `D` (hopefully `$` is only used in identifier names).
2. coqc complains when filenames have a `.` in it before the extension of the file. Replace all `.` within filenames to `_`.
3. The verit parser must be able to parse lets and then we need to add a transformation to remove all lets
Initial experiment to test checker (this checks the checker on the files with their corresponding veriT-new alethe proofs):
1. Run `genBmarks.sh` which will: go through all the `.smt2` files in the directory, add a statement to check the file with its corresponding `.smt2.proof` file to 
    `qfuf.v` and also create a `.v` file that independently checks this file, add a call to `coqc` on the independent files to a separate script `coqclist.sh` so that they can be called independently.
2. Run `qfuf.v` and store results in `qfufop`. See how many of the tests return `true` by searching for `true` (or `=true`) in this file. For more fine-grained 
    error-checking, run `coqclist.sh`, store its output in `coqclistop` and check the error trace there.

Final experiment (that should go into the thesis):
- Remove all `.smt2.proof` files because we'll regenerate these proof files along with proofs from the other solver on the same machine.
For each benchmark `bname.smt2`, 
1. Generate `bname.cvc5proof` from cvc5, `bname.veritoldproof` from veriT2016, `bnameveritproof` from veriT.
2. Run each `.smt2` file with its corresponding 3 proof files and check the output.