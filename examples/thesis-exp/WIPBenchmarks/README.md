# Folder Content Description

Created on 11/16, this directory stores all 10 benchmarks for which SMTCoq currently raises an `assertion failed` using cvc5. These are the 10 failed checks from the PhD thesis. Each file is in the `<n><n>` directory (`<n>` is a digit).

All of them raise the exact same exception:
```
"File "trace/smtTrace.ml", line 311, characters 4-10: Assertion failed."
```
SMTCoq creates a doubly linked list with each step of the
proof as a node. All nodes must be linked to their 
predecessor and successor. This assertion is raised when
one of them isn't. The most likely cause is that we 
are creating a proof step that is never referenced.

## Tracing Back

- `01`, `02`, `05`, `06`, `07`, `08` changed from the following error to an assertion failure:
    ```
    Message: | VeritAst.preprocess_certif: failed to preprocess || find_triv_lits_aux: clause doesn't have trivial literals (x and ~x for some x) |
    ```
    This was the fix for the error:
    ```
    Fixing process_trivial to use functions `eq_mod_dneg` and `neg_mod_dneg` for reasoning
    modulo double negation elimination.
    ```
    See `cvc5coqcop5` to `cvc5coqcop6`.
- `03` changed from a failed check to an assertion failure. This was the fix:
    ```
    Implementing process_trivial
    ```
    See `cvc5coqcop4` to `cvc5coqcop5`.
- `04` changed from the following error to an assertion failure:
    ```
    Error: Cerrors.UserError lia.ml: smt_Atom_to_micromega_formula was expecting an LIA formula
    ```
    The fix was:
    ```
    Making unidentified all_simplify holes
    ```
    See `cvc5coqcop2` to `cvc5coqcop3`.
- `09`, `10` changed from a failed check to an assertion failure. This was the fix:
    ```
    After adding term equality/negation check modulo symmetry at any depth of the term.
    ```
    See `cvc5coqcop8` to `cvc5coqcop9`.


## Possible Action Items
- Check the code corresponding to all the implementations
referenced above, maybe we find a bug. This would mainly
be (1) `process_trivial` and its helper functions 
including `eq_mod_dneg` and `neg_mod_dneg` (2) 
`allSimpAST` case of `process_simplify`.
- Pick the smallest example and debug (smallest is `05`, next smalles is `10`)