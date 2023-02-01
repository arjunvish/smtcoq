# Proofs
## Axioms

No axiom should be added. No library adding axioms should be imported,
except:
- Int63 and Array, used in core SMTCoq
- ProofIrrelevance, to be used with care (it is currently used only to
  treat equality over bit vectors and functional arrays, which are
  implemented as dependent types).


## Hints

Every hint should be put in a hint database, whose name starts with
"smtcoq_". There should be a different database for each part of SMTCoq
(e.g., one for each theory). The general database that is used across
the project is named `smtcoq_core`.


# Code organization
## Documentation
Every OCaml module comes with a documented interface.

## Theories

Theories are organized in sub-directories whose names are the names of
each theory.


## Compilation

Before pushing or making a pull request to the master branch, make sure
that the project compiles with both standard and native Coq.
