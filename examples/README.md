# File Structure
The folder is organized as follows.
- `aletheTests` contains all examples related to the new Alete checker.
- `regress` contains a set of regressions that must all pass everytime changes are made to the Alethe checker. Run regressions by running `make test` in the examples folder.
- `stepDebugger` contains a Python debugger (developed by Polina Kozyarchuk) that given an SMT file and a proof file for which the SMTCoq checker returns `false`, goes through the proof certificate step-by-step and attempts to locate which step the checker fails at.
- `thesis-exp` contains a subset of a Sledgehammer benchmark set that was used to test the Alethe checker as part of Arjun Viswanathan's PhD thesis.

## Regressions
Every time the alethe checker is extended, it **must** pass all regressions before being 
committed. To run regressions, run the following from within the `examples` folder:
```
make test TIMEOUT=n
```
where `n` is the number of seconds to timeout each regression (defaults to 120).