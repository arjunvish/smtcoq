Require Import SMTCoq.SMTCoq.

Variables (A : Type).

Lemma filter_map : forall (f g : A -> bool) (l : list A),
      filter f l = filter g l <-> map f l = map g l.
    Proof.
      intros f g l; induction l as [| a l IHl]; [firstorder|].
      simpl. destruct (f a) eqn:Hfa; destruct (g a) eqn:Hga; split; intros H.
      - inversion H as [H1]. apply IHl in H1. rewrite H1. reflexivity.
      - inversion H as [H1]. apply IHl in H1. rewrite H1. reflexivity.
      - assert (Ha : In a (filter g l)). { rewrite <- H. apply in_eq. }
        apply filter_In in Ha. destruct Ha as [_ Hga']. (* verit. *)
(* Anomaly
"Uncaught exception Failure("Atom op_1 (aka g) is not of the expected type")."  
Please report at http://coq.inria.fr/bugs/.
Discarding the following lemma (unsupported): (filter f l = filter g l <-> map f l = map g l)
[Lemma,SMTCoq plugin]
*)
        rewrite Hga in Hga'. inversion Hga'.
        - inversion H.
        - assert (Ha : In a (filter f l)). { rewrite H. apply in_eq. }
        apply filter_In in Ha. destruct Ha as [_ Hfa']. rewrite Hfa in  
        Hfa'. inversion Hfa'.
      - inversion H.
      - rewrite IHl in H. rewrite H. reflexivity.
      - inversion H. apply IHl. assumption.
    Qed.