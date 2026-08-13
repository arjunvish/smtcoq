(* Demonstrates the mkCongrPred polarity fix in src/verit/veritSyntax.ml.

   `mkCongrPred` (used for veriT's `eq_congruent_pred` rule) picked out the predicate
   congruence's two occurrences - `concl` (the positive, new-argument occurrence) and
   `prem_P` (the negative, old-argument occurrence) - by fixed POSITION: the last literal
   of the declared clause was always assumed to be `concl`, the second-to-last always
   `prem_P`. veriT doesn't guarantee that order for a non-symmetric predicate like `<=`:
   here `t1`'s clause is `[Not(a=c); Not(b=d); (<=c d); Not(<=a b)]` - the POSITIVE
   occurrence (<=c d) comes *before* the NEGATIVE one (Not(<=a b)), the opposite of what
   the old position-only code assumed. That silently swapped `concl`/`prem_P`, feeding
   `process_congr` the predicate's old/new arguments in the wrong roles - `t1` still
   built *some* congruence certificate (no crash), just not the one needed, so the final
   resolution step doesn't reach the empty clause and the checker returns `false` with no
   individual step flagged as invalid.

   Fix: pick `concl`/`prem_P` from the last two literals by polarity (`Form.is_pos`)
   instead of fixed position.

   Found while fixing `examples/aletheTests/sanitychecktests/test7verit.v`, which hits
   this exact bug via `<=` in a nested-`ite` arithmetic normalization (t58 there);
   this file is a minimal, standalone, hand-written reproduction of the same shape,
   confirmed to return `false` before this fix and `true` after it. *)

Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.
Require Import ZArith.
Require Import Int31.
Local Open Scope int31_scope.

Section EqCongruentPredPolarity.
  Verit_Checker "eqcongruentpred_polarity.smt2" "eqcongruentpred_polarity.veritpf".
End EqCongruentPredPolarity.
