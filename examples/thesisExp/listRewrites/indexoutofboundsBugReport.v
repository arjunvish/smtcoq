Require Import SMTCoq.SMTCoq.

Variables (A : Type).

Lemma ext_in_filter : forall (f g : A -> bool) (l : list A),
      filter f l = filter g l -> (forall a, In a l -> f a = g a).
    Proof.
      intros f g l H. intros. Fail verit.
Abort.