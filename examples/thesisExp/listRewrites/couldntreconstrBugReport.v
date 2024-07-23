Require Import SMTCoq.SMTCoq.

Lemma in_seq len start n :
    In n (seq start len) <-> start <= n < start+len.
  Proof.
   revert start. induction len as [|len IHlen]; simpl; intros.
   - rewrite <- plus_n_O. split;[easy|].
     intros (H,H'). abduce 1.
(*
Could not reconstruct abduct
Discarding the following lemma (unsupported): (start <= n)
[Lemma,SMTCoq plugin]
Discarding the following lemma (unsupported): (n < start)
[Lemma,SMTCoq plugin]
*)
(* This is the effective SMT fails for which cvc5 fails:
(set-option :print-success true)
(set-option :produce-assignments true)
(set-logic QF_SAT)
(get-abduct A false)
*)
Abort.