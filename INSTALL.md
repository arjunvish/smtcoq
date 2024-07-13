# Installation and Experimental Evaluation

This branch of SMTCoq serves to provide the experiment sets and the isntructions
to rerun them from the thesis titled "Automating Interactive Theorem Provers and 
Certifying Automated Theorem Provers". All experiments can be found in 
`examples/thesisExp`.

## Requirements
- SMTCoq is designed to work on computers equipped with a POSIX (Unix or a clone) operating system. 
It is known to work under GNU/Linux (i386 and amd64) and Mac OS X.

- [Coq 8.13.2](https://github.com/coq/coq/releases/tag/V8.13.2)

- You will also need to [install the provers](#install-the-provers)
you want to use.



## Installation from the sources, using opam

### Install opam

We recommended to install the required packages from
[opam](https://opam.ocaml.org). Once you have installed opam on your system you
should issue the following command:

```bash
opam init
```

which will initialize the opam installation and prompt for modifying the shell
init file.

Once opam is installed you should still issue

```bash
eval `opam config env`
```

(this is not necessary if you start another session in your shell).

You need to have OCaml version >= 4.11.1 and Coq version 8.13.2.

> **Warning**: The version of Coq that you plan to use must have been compiled
> with the same version of OCaml that you are going to use to compile
> SMTCoq. In particular this means you want a version of Coq that was compiled
> with OCaml version >= 4.11.1.

### Install OCaml

Now you can install an OCaml compiler (we recommend 4.11.1):

```bash
opam switch create thesis24 ocaml-base-compiler.4.11.1
```

### Install Coq

After OCaml is installed, you can install Coq-8.13.2 through opam.

```bash
opam install coq.8.13.2
```

If you also want to install CoqIDE at the same time you can do

```bash
opam install coq.8.13.2 coqide.8.13.2
```
but you might need to install some extra packages and libraries for your system
(such as GTK2, gtksourceview2, etc.).

The num library must also be installed to make this branch of SMTCoq work

```bash
opam install num
```

### Install SMTCoq
Compile and install (installation isn't necessary for running the experiments,
the `_CoqProject` file in each directory identifies SMTCoq's location).

```bash
make
make install
```

## Install the provers

The following solvers need to be installed. Please download/install the solvers you would like to use via the links in the following
subsections (since SMTCoq might not support other versions)
- [CVC4](https://cvc4.github.io/)

- [veriT](https://verit.loria.fr)

- [cvc5](https://cvc5.github.io/)


### CVC4

Use the stable version 1.6 of CVC4 that is available either:
- as a [Linux binary](http://cvc4.cs.stanford.edu/downloads/builds/x86_64-linux-opt/cvc4-1.6-x86_64-linux-opt)
- as a [MacOs binary](https://github.com/cvc5/cvc5/releases/download/1.6/cvc4-1.6-macos-opt)
- from [the sources](https://github.com/cvc5/cvc5/releases/tag/1.6),

Whatever solution you choose, a binary called `cvc4` must be present in
your PATH to use it through SMTCoq.

In your `.bashrc` (or `.bash_profile`, or any other initialization file read by
your shell), export the following environment variable to make it point at the
`signatures` directory distributed with SMTCoq.

> Don't use `~` in the path but rather `$HOME`.

```bash
export LFSCSIGS="$HOME/path/to/smtcoq/src/lfsc/tests/signatures/"
```

If you don't want SMTCoq to spit the translated proof in your proof environment
window, add the following optional definition (in the same file).

```bash
export DONTSHOWVERIT="yes"
```


### veriT

Download this [snapshot of
veriT](https://www.lri.fr/~keller/Documents-recherche/Smtcoq/veriT9f48a98.tar.gz)
which is known compatible with SMTCoq, and is already in proof
production mode. To compile it, unpack the archive and use the following
commands:
```
./configure
make
```
This will produce an executable called `veriT` that you should add to
your path. If you encounter problems to compile it, please report an
issue.


### cvc5

cvc5 versions [1.1.0](https://github.com/cvc5/cvc5/releases/tag/cvc5-1.1.0) and 
[1.1.2](https://github.com/cvc5/cvc5/releases/tag/cvc5-1.1.2).
The `cvc5` binary must be present in your PATH to use it through SMTCoq.


## Setting up environment for SMTCoq
### Emacs and ProofGeneral

If you use Emacs and ProofGeneral for Coq development, we recommend to use the
package [exec-path-from-shell](https://github.com/purcell/exec-path-from-shell)
(which can be installed with `M-x package-install exec-path-from-shell`) and to
add the following in your `.emacs`:

```elisp
(exec-path-from-shell-initialize)
```

This will make emacs use the same environment as your shell. This is also
particularly useful if you have installed Coq and OCaml from opam.

## Running Experiments
See instructions from the `Run Experiments` section of `examples/thesisExp/Exp.md`.
