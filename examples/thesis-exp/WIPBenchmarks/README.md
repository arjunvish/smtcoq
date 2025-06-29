# Folder Content Description

Created on 11/16/24, this directory stores all 7 benchmarks for which SMTCoq currently fails using cvc5. 
Each file is in the `<n><n>` directory (`<n>` is a digit).

10 benchmarks including this one used to raise the exact same exception:
```
"File "trace/smtTrace.ml", line 311, characters 4-10: Assertion failed."
```
## Solution
The issue was that when `process_trivial` removes a step `t` that derive trivial clauses from the certif, it sometimes leaves behind other steps that become unused since `t` is the only step that uses them. Instead of dealing with this within `process_trivial`, I have added a transformation process_unused which goes through the certificate and recursively removes all unused steps. That seems to have fixed the issue.

Now, the checker returns `false` for 7 of these 10: `01`, `02`, `03`, `04`, `06`, `07`, `08`.

The following is from the previous iteration of the experiments before the unused clause removal problem was
solved.

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

