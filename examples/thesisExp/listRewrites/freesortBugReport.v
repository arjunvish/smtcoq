Require Import SMTCoq.SMTCoq.

Lemma seq_NoDup len start : NoDup (seq start len).
  Proof.
   revert start; induction len; simpl; constructor; trivial.
   rewrite in_seq. intros (H,_). Fail abduce 1.
(*
Discarding the following lemma (unsupported): ((forall H0 : nat, NoDup (seq H0 len)) : Prop)
[Lemma,SMTCoq plugin]
Discarding the following lemma (unsupported): (S start <= start : Prop)
[Lemma,SMTCoq plugin]
The command has indeed failed with message:
Solver error: (error Parse Error: <stdin>:4.13: Free sort symbols not allowed in QF_SAT ).
*)
Abort.