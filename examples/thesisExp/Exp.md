Assuming you're in a Linux-based system (tested on Ubuntu 20.04),
the following provide a complete set of instructions to run our experiments
on the abduce tactic.

## 1. Download the solvers from the links and add them to your path:
- cvc5 (experiments on ZOrder and Z.Mul were run with version [1.1.0](https://github.com/cvc5/cvc5/releases/tag/cvc5-1.1.0) and experiments on List were run with version [1.1.2](https://github.com/cvc5/cvc5/releases/tag/cvc5-1.1.2))
- [cvc4](http://cvc4.cs.stanford.edu/downloads/builds/x86_64-linux-opt/cvc4-1.6-x86_64-linux-opt)
- [veriT](https://www.lri.fr/~keller/Documents-recherche/Smtcoq/veriT9f48a98.tar.gz)

## 2. Set up environment for cvc4
In your `.bashrc` (or `.bash_profile`, or any other initialization file read by
your shell), export the following environment variable to make it point at the
`signatures` directory distributed with SMTCoq.

> Don't use `~` in the path but rather `$HOME`.

```bash
export LFSCSIGS="$HOME/path/to/smtcoq/src/lfsc/tests/signatures/"
```

## 3. Install SMTCoq
Assuming [opam](https://opam.ocaml.org) is installed:
```
opam switch create thesis24 ocaml-base-compiler.4.11.1
opam install coq.8.13.2 coqide.8.13.2
git clone https://github.com/arjunvish/smtcoq.git
cd smtcoq/src/
git checkout thesis24
make
```

## 4. Run Experiments
Assuming you are in `./src/`:
```
cd ../examples/
```
The Coq files for each experiment are in their separate directory. The `results.csv` file in 
each directory enlists the results for each test case.

### Experiments over the ZOrder library
Navigate to `01Zorder` and open `ZOrder.v` with CoqIDE:
```
cd 01ZOrder
coqide Zorder.v
```
Now the file can be checked either step-by-step
(Navigation -> forward), or to the end
(Navigation -> Run to end) via CoqIDE. Expected outputs 
are commented after each goal.

### Experiments over the List library
Experiments are run over the Coq standard library's `List.v`; the experiments over `apply` tactics
and `rewrite` tactics are separated into `List-apply.v` and `List-rewrite.v`. Navigate into the `02List`
and open each of them in CoqIDE to see the commented calls to SMTCoq's tactics and their 
results (also in comments).
```
cd 02List
coqide List-apply.v List-rewrite.v
```
Each test unit is preceded by a comment `(* GOAL #n )` where `n` is the goal number.

### Experiments over Z.Mul
Experiments are run over files from the Coq standard library that use lemmas over multiplication. All files 
can be found in `03Mul` and the goals are spread across the files and can be identified by the `(* Test Unit *)`
comment. This is followed by a comment that identifies the goal from `results.csv`, the call to `abduce`, 
and the output of the call.