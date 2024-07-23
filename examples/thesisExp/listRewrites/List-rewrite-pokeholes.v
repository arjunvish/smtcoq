   (************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General  Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Setoid.
Require Import PeanoNat Le Gt Minus Bool Lt.
  
Set Implicit Arguments.
(* Set Universe Polymorphism. *) 
 
(******************************************************************)
(** * Basics: definition of polymorphic lists and some operations *)
(******************************************************************)

(** The definition of [list] is now in [Init/Datatypes],
    as well as the definitions of [length] and [app] *)
 
(*Add Rec LoadPath "/home/arjun/Desktop/smtcoq/smtcoq/src" as SMTCoq.*)
Require Import SMTCoq.SMTCoq.

Open Scope list_scope.

(** Standard notations for lists.
In a special module to avoid conflicts. *)
Module ListNotations.
Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x ; y ; .. ; z ]" :=  (cons x (cons y .. (cons z nil) ..)) : list_scope.
End ListNotations.

Import ListNotations.

Section Lists. 

  Variable A : Type.

  (** Head and tail *)

  Definition hd (default:A) (l:list A) :=
    match l with
      | [] => default
      | x :: _ => x
    end.

  Definition hd_error (l:list A) :=
    match l with
      | [] => None
      | x :: _ => Some x
    end.

  Definition tl (l:list A) :=
    match l with
      | [] => nil
      | a :: m => m
    end.

  (** The [In] predicate *)
  Fixpoint In (a:A) (l:list A) : Prop :=
    match l with
      | [] => False
      | b :: m => b = a \/ In a m
    end.

End Lists.

Section Facts.

  Variable A : Type.


  (** *** Generic facts *)

  (** Discrimination *)
  Theorem nil_cons (x:A) (l:list A) : [] <> x :: l.
  Proof.
    discriminate.
  Qed.


  (** Destruction *)

  Theorem destruct_list (l : list A) : {x:A & {tl:list A | l = x::tl}}+{l = []}.
  Proof.
    induction l as [|a tail].
    right; reflexivity.
    left; exists a, tail; reflexivity.
  Qed.

  Lemma hd_error_tl_repr l (a:A) r :
    hd_error l = Some a /\ tl l = r <-> l = a :: r.
  Proof. destruct l as [|x xs].
    - unfold hd_error, tl; split; firstorder discriminate.
    - intros. simpl. split.
      * intros (H1, H2). inversion H1. (* verit. admit. admit. *)
        (* GOAL #1: *) (* Fail Timeout 20 (time abduce 2).*)
        (* OUTPUT #1: Unexpectedly succeeds. Need to investigate *)
        (* RESULT #1: Smt Success. *)
        rewrite H2. reflexivity.
      * inversion 1. subst. auto.
  Qed.

  Lemma hd_error_some_nil l (a:A) : hd_error l = Some a -> l <> nil.
  Proof. unfold hd_error. destruct l; now discriminate. Qed.

  Theorem length_zero_iff_nil (l : list A):
    length l = 0 <-> l=[].
  Proof.
    split; [now destruct l | now intros ->].
  Qed.

  (** *** Head and tail *)

  Theorem hd_error_nil : hd_error (@nil A) = None.
  Proof.
    simpl; reflexivity.
  Qed.

  Theorem hd_error_cons (l : list A) (x : A) : hd_error (x::l) = Some x.
  Proof.
    simpl; reflexivity.
  Qed.


  (**************************)
  (** *** Facts about [app] *)
  (**************************)

  (** Discrimination *)
  Theorem app_cons_not_nil (x y:list A) (a:A) : [] <> x ++ a :: y.
  Proof.
    unfold not.
    destruct x; simpl; intros H.
    discriminate H.
    discriminate H.
  Qed.


  (** Concat with [nil] *)
  Theorem app_nil_l (l:list A) : [] ++ l = l.
  Proof.
    reflexivity.
  Qed.

  Theorem app_nil_r (l:list A) : l ++ [] = l.
  Proof.
    induction l; simpl; f_equal; auto.
  Qed.

  (* begin hide *)
  (* Deprecated *)
  Theorem app_nil_end (l:list A) : l = l ++ [].
  Proof. symmetry; apply app_nil_r. Qed.
  (* end hide *)

  (** [app] is associative *)
  Theorem app_assoc (l m n:list A) : l ++ m ++ n = (l ++ m) ++ n.
  Proof.
    induction l; simpl; f_equal; auto.
  Qed.

  (* begin hide *)
  (* Deprecated *)
  Theorem app_assoc_reverse (l m n:list A) : (l ++ m) ++ n = l ++ m ++ n.
  Proof.
     auto using app_assoc.
  Qed.
  #[local]
  Hint Resolve app_assoc_reverse : core.
  (* end hide *)

  (** [app] commutes with [cons] *)
  Theorem app_comm_cons (x y:list A) (a:A) : a :: (x ++ y) = (a :: x) ++ y.
  Proof.
    auto.
  Qed.

  (** Facts deduced from the result of a concatenation *)

  Theorem app_eq_nil (l l':list A) : l ++ l' = [] -> l = [] /\ l' = [].
  Proof.
    destruct l as [| x l]; destruct l' as [| y l']; simpl; auto.
    intro; discriminate.
    intros H; discriminate H.
  Qed.

  Theorem app_eq_unit (x y:list A) (a:A) :
      x ++ y = [a] -> x = [] /\ y = [a] \/ x = [a] /\ y = [].
  Proof.
    destruct x as [|a' l]; [ destruct y as [|a' l] | destruct y as [| a0 l0] ];
      simpl.
    intros H; discriminate H.
    left; split; auto.
    intro H; right; split; auto.
    generalize H.
    generalize (app_nil_r l); intros E. (* verit. admit. admit. *)
    (* GOAL #2: *) (* Fail Timeout 20 (time abduce 2).*)
    (* OUTPUT #2: Unexpectedly succeeds. Need to investigate *)
    (* RESULT #2: Smt Success. *)
    rewrite -> E; auto.
    intros H.
    injection H as [= H H0].
    assert ([] = l ++ a0 :: l0) as H1 by auto.
    apply app_cons_not_nil in H1 as [].
  Qed.

  Lemma elt_eq_unit l1 l2 (a b : A) :
    l1 ++ a :: l2 = [b] -> a = b /\ l1 = [] /\ l2 = [].
  Proof.
    intros Heq.
    apply app_eq_unit in Heq.
    now destruct Heq as [[Heq1 Heq2]|[Heq1 Heq2]]; inversion_clear Heq2.
  Qed.

  Lemma app_inj_tail_iff :
    forall (x y:list A) (a b:A), x ++ [a] = y ++ [b] <-> x = y /\ a = b.
  Proof.
    intro x; induction x as [| x l IHl]; intro y;
      [ destruct y as [| a l] | destruct y as [| a l0] ];
      simpl; auto.
    - intros a b. split.
      + intros [= ]. auto.
      + intros [H0 H1]. subst. auto.
    - intros a0 b. split.
      + intros [= H1 H0]. apply app_cons_not_nil in H0 as [].
      + intros [H0 H1]. inversion H0.
    - intros a b. split.
      + intros [= H1 H0]. assert ([] = l ++ [a]) as H by auto. apply app_cons_not_nil in H as [].
      + intros [H0 H1]. inversion H0.
    - intros a0 b. split.
      + intros [= <- H0]. specialize (IHl l0 a0 b). apply IHl in H0. destruct H0. subst. split; auto.
      + intros [H0 H1]. inversion H0. subst. auto.
  Qed.

  Lemma app_inj_tail :
    forall (x y:list A) (a b:A), x ++ [a] = y ++ [b] -> x = y /\ a = b.
  Proof.
    apply app_inj_tail_iff.
  Qed.

  (** Compatibility with other operations *)

  Lemma app_length : forall l l' : list A, length (l++l') = length l + length l'.
  Proof.
    intro l; induction l; simpl; auto.
  Qed.

  Lemma last_length : forall (l : list A) a, length (l ++ a :: nil) = S (length l).
  Proof.
    intros. 
    (* GOAL #3: *) 
    (* assert (length [a] = 1) by admit.
    assert (length l + 1 = S (length l + 0)) by admit.
    assert (length l + 0 = length l) by admit.
    Fail Timeout 20 (time abduce 1). *)
    (* OUTPUT #3: 
The command has indeed failed with message:
Timeout! *)
    (* RESULT #3: Failure. Poked holes. *) rewrite app_length. 
    simpl.
    (* GOAL #4: *) 
    (* assert (length l + 0 = length l) by admit. 
    Fail Timeout 20 (time abduce 1). *)
    (* OUTPUT #4:
Tactic call ran for 3.724 secs (0.u,0.023s) (failure)
The command has indeed failed with message:
cvc5 returned SAT.
The solver cannot prove the goal, but one of the following hypotheses (printed in Prop, but the corresponding Boolean versions also apply) would make it provable:
((length (A:=A)) l) = 0 && (S 0) = 0 *)
    (* RESULT #4: Failure. Poked holes. *)
    rewrite <- plus_n_Sm.
    (* GOAL #5: *) (* Fail Timeout 20 (time abduce 1). *)
    (* OUTPUT #5: 
Tactic call ran for 0.65 secs (0.003u,0.032s) (failure)
The command has indeed failed with message:
cvc5 returned SAT.
The solver cannot prove the goal, but one of the following hypotheses (printed in Prop, but the corresponding Boolean versions also apply) would make it provable:
(Init.Nat.add ((length (A:=A)) l) 0) = ((length (A:=A)) l)*)
(*assert ((Init.Nat.add ((length (A:=A)) l) 0) = ((length (A:=A)) l)). {
Search (_ + 0 = _). apply Nat.add_0_r. } smt.
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.*)
(* RESULT #5: Success. smt fails on Nat goal. *)
rewrite plus_n_O; reflexivity.
  Qed.

  Lemma app_inv_head_iff:
   forall l l1 l2 : list A, l ++ l1 = l ++ l2 <-> l1 = l2.
  Proof.
    intro l; induction l as [|? l IHl]; split; intros H; simpl; auto.
    - apply IHl. inversion H. auto.
    - subst. auto.
  Qed.

  Lemma app_inv_head:
   forall l l1 l2 : list A, l ++ l1 = l ++ l2 -> l1 = l2.
  Proof.
    apply app_inv_head_iff.
  Qed.

  Lemma app_inv_tail:
    forall l l1 l2 : list A, l1 ++ l = l2 ++ l -> l1 = l2.
  Proof.
    intros l l1 l2; revert l1 l2 l.
    intro l1; induction l1 as [ | x1 l1]; intro l2; destruct l2 as [ | x2 l2];
     simpl; auto; intros l H.
    absurd (length (x2 :: l2 ++ l) <= length l).
    simpl. (* GOAL #6: *) (* Fail Timeout 20 (time abduce 1). *)
           (* OUTPUT #6: 
Tactic call ran for 0.005 secs (0.005u,0.s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.*)
    (* RESULT #6: N/A. Nat predicate. *)
    rewrite app_length. auto with arith.
    
    (* GOAL #7: *) (* Fail Timeout 20 (time abduce 1). *)
    (* OUTPUT #7:
Tactic call ran for 0.009 secs (0.009u,0.s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.*)
    (* RESULT #7: N/A. Local lemma. Nat Predicate. *)
    rewrite <- H. auto with arith.
    absurd (length (x1 :: l1 ++ l) <= length l).
    simpl. (* GOAL #8: *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #8:
Tactic call ran for 0.03 secs (0.03u,0.s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.*)
(* RESULT #8: N/A. Nat predicate. *)
    rewrite app_length. auto with arith.
    (* GOAL #9: *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #9:
Tactic call ran for 0.025 secs (0.024u,0.s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.*)
(* RESULT #9: N/A. Local lemma. Nat Predicate. *)
    rewrite H. auto with arith.
    injection H as [= H H0]; f_equal; eauto.
  Qed.

  Lemma app_inv_tail_iff:
    forall l l1 l2 : list A, l1 ++ l = l2 ++ l <-> l1 = l2.
  Proof.
    split; [apply app_inv_tail | now intros ->].
  Qed.

  (************************)
  (** *** Facts about [In] *)
  (************************)


  (** Characterization of [In] *)

  Theorem in_eq : forall (a:A) (l:list A), In a (a :: l).
  Proof.
    simpl; auto.
  Qed.

  Theorem in_cons : forall (a b:A) (l:list A), In b l -> In b (a :: l).
  Proof.
    simpl; auto.
  Qed.

  Theorem not_in_cons (x a : A) (l : list A):
    ~ In x (a::l) <-> x<>a /\ ~ In x l.
  Proof.
    simpl. intuition.
  Qed.

  Theorem in_nil : forall a:A, ~ In a [].
  Proof.
    unfold not; intros a H; inversion_clear H.
  Qed.

  Lemma in_app_or : forall (l m:list A) (a:A), In a (l ++ m) -> In a l \/ In a m.
  Proof.
    intros l m a.
    elim l; simpl; auto.
    intros a0 y H H0.
    now_show ((a0 = a \/ In a y) \/ In a m).
    elim H0; auto.
    intro H1.
    now_show ((a0 = a \/ In a y) \/ In a m).
    elim (H H1); auto.
  Qed.

  Lemma in_or_app : forall (l m:list A) (a:A), In a l \/ In a m -> In a (l ++ m).
  Proof.
    intros l m a.
    elim l; simpl; intro H.
    now_show (In a m).
    elim H; auto; intro H0.
    now_show (In a m).
    elim H0. (* subProof completed *)
    intros y H0 H1.
    now_show (H = a \/ In a (y ++ m)).
    elim H1; auto 4.
    intro H2.
    now_show (H = a \/ In a (y ++ m)).
    elim H2; auto.
  Qed.

  Lemma in_app_iff : forall l l' (a:A), In a (l++l') <-> In a l \/ In a l'.
  Proof.
    split; auto using in_app_or, in_or_app.
  Qed.

  Theorem in_split : forall x (l:list A), In x l -> exists l1 l2, l = l1++x::l2.
  Proof.
  intros x l; induction l as [|a l IHl]; simpl; [destruct 1|destruct 1 as [?|H]].
  subst a; auto.
  exists [], l; auto.
  destruct (IHl H) as (l1,(l2,H0)).
  exists (a::l1), l2; simpl. apply f_equal. auto.
  Qed.

  Lemma in_elt : forall (x:A) l1 l2, In x (l1 ++ x :: l2).
  Proof.
  intros.
  apply in_or_app.
  right; left; reflexivity.
  Qed.

  Lemma in_elt_inv : forall (x y : A) l1 l2,
    In x (l1 ++ y :: l2) -> x = y \/ In x (l1 ++ l2).
  Proof.
  intros x y l1 l2 Hin.
  apply in_app_or in Hin.
  destruct Hin as [Hin|[Hin|Hin]]; [right|left|right]; try apply in_or_app; intuition.
  Qed.

  (** Inversion *)
  Lemma in_inv : forall (a b:A) (l:list A), In b (a :: l) -> a = b \/ In b l.
  Proof. easy. Qed.

  (** Decidability of [In] *)
  Theorem in_dec :
    (forall x y:A, {x = y} + {x <> y}) ->
    forall (a:A) (l:list A), {In a l} + {~ In a l}.
  Proof.
    intros H a l; induction l as [| a0 l IHl].
    right; apply in_nil.
    destruct (H a0 a); simpl; auto.
    destruct IHl; simpl; auto.
    right; unfold not; intros [Hc1| Hc2]; auto.
  Defined.



End Facts.

#[global]
Hint Resolve app_assoc app_assoc_reverse: datatypes.
#[global]
Hint Resolve app_comm_cons app_cons_not_nil: datatypes.
#[global]
Hint Immediate app_eq_nil: datatypes.
#[global]
Hint Resolve app_eq_unit app_inj_tail: datatypes.
#[global]
Hint Resolve in_eq in_cons in_inv in_nil in_app_or in_or_app: datatypes.



(*******************************************)
(** * Operations on the elements of a list *)
(*******************************************)

Section Elts.

  Variable A : Type.

  (*****************************)
  (** ** Nth element of a list *)
  (*****************************)

  Fixpoint nth (n:nat) (l:list A) (default:A) {struct l} : A :=
    match n, l with
      | O, x :: l' => x
      | O, other => default
      | S m, [] => default
      | S m, x :: t => nth m t default
    end.

  Fixpoint nth_ok (n:nat) (l:list A) (default:A) {struct l} : bool :=
    match n, l with
      | O, x :: l' => true
      | O, other => false
      | S m, [] => false
      | S m, x :: t => nth_ok m t default
    end.

  Lemma nth_in_or_default :
    forall (n:nat) (l:list A) (d:A), {In (nth n l d) l} + {nth n l d = d}.
  Proof.
    intros n l d; revert n; induction l as [|? ? IHl].
    - intro n; right; destruct n; trivial.
    - intros [|n]; simpl.
      * left; auto.
      * destruct (IHl n); auto.
  Qed.

  Lemma nth_S_cons :
    forall (n:nat) (l:list A) (d a:A),
      In (nth n l d) l -> In (nth (S n) (a :: l) d) (a :: l).
  Proof.
    simpl; auto.
  Qed.

  Fixpoint nth_error (l:list A) (n:nat) {struct n} : option A :=
    match n, l with
      | O, x :: _ => Some x
      | S n, _ :: l => nth_error l n
      | _, _ => None
    end.

  Definition nth_default (default:A) (l:list A) (n:nat) : A :=
    match nth_error l n with
      | Some x => x
      | None => default
    end.

  Lemma nth_default_eq :
    forall n l (d:A), nth_default d l n = nth n l d.
  Proof.
    unfold nth_default; intro n; induction n; intros [ | ] ?; simpl; auto.
  Qed.

  (** Results about [nth] *)

  Lemma nth_In :
    forall (n:nat) (l:list A) (d:A), n < length l -> In (nth n l d) l.
  Proof.
    unfold lt; intro n; induction n as [| n hn]; simpl; intro l.
    - destruct l; simpl; [ inversion 2 | auto ].
    - destruct l; simpl.
      * inversion 2.
      * intros d ie; right; apply hn; auto with arith.
  Qed.

  Lemma In_nth l x d : In x l ->
    exists n, n < length l /\ nth n l d = x.
  Proof.
    induction l as [|a l IH].
    - easy.
    - intros [H|H].
      * subst; exists 0; simpl; auto with arith.
      * destruct (IH H) as (n & Hn & Hn').
        exists (S n); simpl; auto with arith.
  Qed.

  Lemma nth_overflow : forall l n d, length l <= n -> nth n l d = d.
  Proof.
    intro l; induction l as [|? ? IHl]; intro n; destruct n;
     simpl; intros d H; auto.
    - inversion H.
    - apply IHl; auto with arith.
  Qed.

  Lemma nth_indep :
    forall l n d d', n < length l -> nth n l d = nth n l d'.
  Proof.
    intro l; induction l.
    - inversion 1.
    - intros [|n] d d'; simpl; auto with arith.
  Qed.

  Lemma app_nth1 :
    forall l l' d n, n < length l -> nth n (l++l') d = nth n l d.
  Proof.
    intro l; induction l.
    - inversion 1.
    - intros l' d [|n]; simpl; auto with arith.
  Qed.

  Lemma app_nth2 :
    forall l l' d n, n >= length l -> nth n (l++l') d = nth (n-length l) l' d.
  Proof.
    intro l; induction l as [|? ? IHl]; intros l' d [|n]; auto.
    - inversion 1.
    - intros. simpl. 
(* GOAL #10: *) (* Fail Timeout 20 (time abduce 1). *)
(* RESULT #10: N/A. Quantified. *) 
rewrite IHl; auto with arith.
  Qed.

  Lemma app_nth2_plus : forall l l' d n,
    nth (length l + n) (l ++ l') d = nth n l' d.
  Proof.
    intros.
(* GOAL #11: *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #11:
The command has indeed failed with message:
Timeout!*)
(* RESULT #11: Failure. Can't poke holes. *)
    rewrite app_nth2. 
(* GOAL #12: *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #12:
Tactic call ran for 13.581 secs (0.u,0.019s) (failure)
The command has indeed failed with message:
cvc5 returned SAT.
The solver cannot prove the goal, but one of the following hypotheses (printed in Prop, but the corresponding Boolean versions also apply) would make it provable:
(Init.Nat.sub (Init.Nat.add ((length (A:=A)) l) n) ((length (A:=A)) l)) = n*)
(*assert ((Init.Nat.sub (Init.Nat.add ((length (A:=A)) l) n) ((length (A:=A)) l)) = n). { Search (_ + _ - _ = _). apply minus_plus. } smt.*)
(* RESULT #12: Success. *)
    rewrite minus_plus. trivial.
    auto with arith.
  Qed.

  Lemma nth_middle : forall l l' a d,
    nth (length l) (l ++ a :: l') d = a.
  Proof.
    intros.
    (* GOAL #13: *) 
    (* assert (nth (length l + 0) (l ++ a :: l') d = a) by admit.
    Fail Timeout 20 (time abduce 1). 
    assert ((Init.Nat.add ((length (A:=A)) l) 0) = ((length (A:=A)) l)). 
    { Search (_ + 0 = _). apply Nat.add_0_r. } smt. *)
    (* OUTPUT #13: 
Tactic call ran for 3.774 secs (0.012u,0.012s) (failure)
The command has indeed failed with message:
cvc5 returned SAT.
The solver cannot prove the goal, but one of the following hypotheses (printed in Prop, but the corresponding Boolean versions also apply) would make it provable:
(Init.Nat.add ((length (A:=A)) l) 0) = ((length (A:=A)) l) *)
    (* RESULT #13: Success. Poked holes. *)
    rewrite plus_n_O at 1.
    apply app_nth2_plus.
  Qed.

  Lemma nth_split n l d : n < length l ->
    exists l1, exists l2, l = l1 ++ nth n l d :: l2 /\ length l1 = n.
  Proof.
    revert l.
    induction n as [|n IH]; intros [|a l] H; try easy.
    - exists nil; exists l; now simpl.
    - destruct (IH l) as (l1 & l2 & Hl & Hl1); auto with arith.
      exists (a::l1); exists l2; simpl; split; now f_equal.
  Qed.

  Lemma nth_ext : forall l l' d d', length l = length l' ->
    (forall n, n < length l -> nth n l d = nth n l' d') -> l = l'.
  Proof.
    intro l; induction l as [|a l IHl];
     intros l' d d' Hlen Hnth; destruct l' as [| b l'].
    - reflexivity.
    - inversion Hlen.
    - inversion Hlen.
    - change a with (nth 0 (a :: l) d).
      change b with (nth 0 (b :: l') d').
      (* GOAL #14: *) (* Fail Timeout 20 (time abduce 1). *)
      (* OUTPUT #14:
Tactic call ran for 0.109 secs (0.066u,0.016s) (failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName11 Tindex_0)) (= op_0 SMTCoqRelName11) ) ).*)
      (* RESULT #14: N/A. Quantified. *)
      rewrite Hnth. f_equal.
      + apply IHl with d d'; [ now inversion Hlen | ].
        intros n Hlen'; apply (Hnth (S n)).
        now simpl; apply lt_n_S.
      + simpl; apply Nat.lt_0_succ.
  Qed.

  (** Results about [nth_error] *)

  Lemma nth_error_In l n x : nth_error l n = Some x -> In x l.
  Proof.
    revert n. induction l as [|a l IH]; intros [|n]; simpl; try easy.
    - injection 1; auto.
    - eauto.
  Qed.

  Lemma In_nth_error l x : In x l -> exists n, nth_error l n = Some x.
  Proof.
    induction l as [|a l IH].
    - easy.
    - intros [H|H].
      * subst; exists 0; simpl; auto with arith.
      * destruct (IH H) as (n,Hn).
        exists (S n); simpl; auto with arith.
  Qed.

  Lemma nth_error_None l n : nth_error l n = None <-> length l <= n.
  Proof.
    revert n. induction l as [|? ? IHl]; intro n; destruct n; simpl.
    - split; auto.
    - split; auto with arith.
    - split; now auto with arith.
    - (* GOAL #15: *) (* Fail Timeout 20 (time abduce 1). *)
      (* OUTPUT #15:
Tactic call ran for 0.014 secs (0.005u,0.008s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.*)
      (* RESULT #15: N/A. Nat predicate. *)
      rewrite IHl. split; auto with arith.
  Qed.

  Lemma nth_error_Some l n : nth_error l n <> None <-> n < length l.
  Proof.
   revert n. induction l as [|? ? IHl]; intro n; destruct n; simpl.
    - split; [now destruct 1 | inversion 1].
    - split; [now destruct 1 | inversion 1].
    - split; now auto with arith.
    - (* GOAL #16: *) (* Fail Timeout 20 (time abduce 1). *)
      (* OUTPUT #16:
Tactic call ran for 0.021 secs (0.021u,0.s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.*)
      (* RESULT #15: N/A. Nat predicate. *)
      rewrite IHl; split; auto with arith.
  Qed.

  Lemma nth_error_split l n a : nth_error l n = Some a ->
    exists l1, exists l2, l = l1 ++ a :: l2 /\ length l1 = n.
  Proof.
    revert l.
    induction n as [|n IH]; intros [|x l] H; simpl in *; try easy.
    - exists nil; exists l. now injection H as [= ->].
    - destruct (IH _ H) as (l1 & l2 & H1 & H2).
      exists (x::l1); exists l2; simpl; split; now f_equal.
  Qed.

  Lemma nth_error_app1 l l' n : n < length l ->
    nth_error (l++l') n = nth_error l n.
  Proof.
    revert l.
    induction n as [|n IHn]; intros [|a l] H; auto; try solve [inversion H].
    simpl in *. apply IHn. auto with arith.
  Qed.

  Lemma nth_error_app2 l l' n : length l <= n ->
    nth_error (l++l') n = nth_error l' (n-length l).
  Proof.
    revert l.
    induction n as [|n IHn]; intros [|a l] H; auto; try solve [inversion H].
    simpl in *. apply IHn. auto with arith.
  Qed.

  (** Results directly relating [nth] and [nth_error] *)

  Lemma nth_error_nth : forall (l : list A) (n : nat) (x d : A),
    nth_error l n = Some x -> nth n l d = x.
  Proof.
    intros l n x d H.
    apply nth_error_split in H. destruct H as [l1 [l2 [H H']]].
    subst. 
    (* GOAL #17: *) (* Fail Timeout 20 (time abduce 1). *)
    (* OUTPUT #17: 
The command has indeed failed with message:
Timeout! *)
    (* RESULT #17: Failure. Can't poke holes. *)
    rewrite app_nth2; [|auto].
    (* GOAL #18: *) (* Fail Timeout 20 (time abduce 1). *)
    (* OUTPUT #18: 
The command has indeed failed with message:
Timeout!*)
    (* RESULT #18: Failure. Can't poke holes. *)
    rewrite Nat.sub_diag. reflexivity.
  Qed.

  Lemma nth_error_nth' : forall (l : list A) (n : nat) (d : A),
    n < length l -> nth_error l n = Some (nth n l d).
  Proof.
    intros l n d H.
    apply (nth_split _ d) in H. destruct H as [l1 [l2 [H H']]].
    subst. 
    (* GOAL #19: *) 
    (* assert (nth_error (l1 ++ nth (length l1) l d :: l2) (length l1) = 
      nth_error (nth (length l1) l d :: l2) (length l1 - length l1))
      by admit.
    assert (Some (nth (length l1) (l1 ++ nth (length l1) l d :: l2) d)
    = Some (nth (length l1 - length l1) (nth (length l1) l d :: l2) d)) 
    by admit.
    assert (Some (nth (length l1 - length l1) (nth (length l1) l d :: l2) d) 
    = Some (nth 0 (nth (length l1) l d :: l2) d)) by admit.
    Fail Timeout 20 (time abduce 1). *)
    (* OUTPUT #19:
The command has indeed failed with message:
Timeout!*)
    (* RESULT #19: Failure. Poked holes. Local lemma. *)
    rewrite H.
    (* GOAL #20: *) (* Fail Timeout 20 (time abduce 1). *)
    (* OUTPUT #20: 
The command has indeed failed with message:
Timeout!*)
    (* RESULT #20: Failure. Can't poke holes. *)
    rewrite nth_error_app2; [|auto].
    (* GOAL #21: *) (* Fail Timeout 20 (time abduce 1). *)
    (* OUTPUT #21: 
The command has indeed failed with message:
Timeout!*)
    (* RESULT #21: Failure. Can't poke holes. *)
    rewrite app_nth2; [| auto].
    (* GOAL #22: *) (* Fail Timeout 20 (time abduce 1). *)
    (* OUTPUT #22: 
The command has indeed failed with message:
Timeout!*)
    (* RESULT #22: Failure. Can't poke holes. *)
    repeat (rewrite Nat.sub_diag). reflexivity.
  Qed.

  (******************************)
  (** ** Last element of a list *)
  (******************************)

  (** [last l d] returns the last element of the list [l],
    or the default value [d] if [l] is empty. *)

  Fixpoint last (l:list A) (d:A) : A :=
  match l with
    | [] => d
    | [a] => a
    | a :: l => last l d
  end.

  Lemma last_last : forall l a d, last (l ++ [a]) d = a.
  Proof.
    intro l; induction l as [|? l IHl]; intros; [ reflexivity | ].
    simpl. (* GOAL #23 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #23: 
Tactic call ran for 0.044 secs (0.007u,0.008s) (failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName0 Tindex_0) (SMTCoqRelName1 Tindex_0)) (= SMTCoqRelName1 (op_4 (op_3 op_0 (op_2 SMTCoqRelName1 op_1)) SMTCoqRelName0)) ) ).*)
(* RESULT #23: N/A. Quantified. Local lemma. *) rewrite IHl.
    destruct l; reflexivity.
  Qed.

  (** [removelast l] remove the last element of [l] *)

  Fixpoint removelast (l:list A) : list A :=
    match l with
      | [] =>  []
      | [a] => []
      | a :: l => a :: removelast l
    end.

  Lemma app_removelast_last :
    forall l d, l <> [] -> l = removelast l ++ [last l d].
  Proof.
    intro l; induction l as [|? l IHl].
    destruct 1; auto.
    intros d _.
    destruct l as [|a0 l]; auto.
    pattern (a0::l) at 1. (* GOAL #24 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #24: 
Tactic call ran for 0.05 secs (0.044u,0.006s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."*)
(* RESULT #24: N/A. Non-bool predicate. *) rewrite IHl with d. auto; discriminate.
    auto; discriminate.
  Qed.

  Lemma exists_last :
    forall l, l <> [] -> { l' : (list A) & { a : A | l = l' ++ [a]}}.
  Proof.
    intro l; induction l as [|a l IHl].
    destruct 1; auto.
    intros _.
    destruct l.
    exists [], a; auto.
    destruct IHl as [l' (a',H)]; try discriminate.
    (* GOAL #25 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #25: 
Tactic call ran for 0.006 secs (0.001u,0.005s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."*)
(* RESULT #25: N/A. Non-bool predicate. Local lemma. *)
    rewrite H.
    exists (a::l'), a'; auto.
  Qed.

  Lemma removelast_app :
    forall l l', l' <> [] -> removelast (l++l') = l ++ removelast l'.
  Proof.
    intro l; induction l as [|? l IHl].
    simpl; auto.
    simpl; intros l' H.
    assert (l++l' <> []) as H0.
    destruct l.
    simpl; auto.
    simpl; discriminate.
    specialize (IHl l' H).
    destruct (l++l'); [elim H0; auto|f_equal; auto].
  Qed.

  Lemma removelast_last : forall l a, removelast (l ++ [a]) = l.
  Proof.
    intros.
    (* GOAL #26 *) 
    (* assert (l ++ removelast [a] = l) by admit. 
       Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #26: 
Tactic call ran for 12.785 secs (0.011u,0.01s) (failure)
The command has indeed failed with message:
cvc5 returned SAT.
The solver cannot prove the goal, but one of the following hypotheses (printed in Prop, but the corresponding Boolean versions also apply) would make it provable:
(removelast ((app (A:=A)) l (cons a []))) = l
*)
(* RESULT #26: Failure. Poked holes. asserts goal. *)
    rewrite removelast_app. apply app_nil_r.
    - intros Heq; inversion Heq.
  Qed.


  (*****************)
  (** ** Remove    *)
  (*****************)

  Hypothesis eq_dec : forall x y : A, {x = y}+{x <> y}.

  Fixpoint remove (x : A) (l : list A) : list A :=
    match l with
      | [] => []
      | y::tl => if (eq_dec x y) then remove x tl else y::(remove x tl)
    end.

  Lemma remove_cons : forall x l, remove x (x :: l) = remove x l.
  Proof.
    intros x l; simpl; destruct (eq_dec x x); [ reflexivity | now exfalso ].
  Qed.

  Lemma remove_app : forall x l1 l2,
    remove x (l1 ++ l2) = remove x l1 ++ remove x l2.
  Proof.
    intros x l1; induction l1 as [|a l1 IHl1]; intros l2; simpl.
    - reflexivity.
    - destruct (eq_dec x a).
      + apply IHl1.
      + (* GOAL #27 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #27: 
Tactic call ran for 0.118 secs (0.096u,0.004s) (failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName3 Tindex_0)) (= (op_3 op_0 (op_2 op_1 SMTCoqRelName3)) (op_2 (op_3 op_0 op_1) (op_3 op_0 SMTCoqRelName3))) ) ).*)
(* RESULT #27: N/A. Quantified. *) rewrite <- app_comm_cons; f_equal.
        apply IHl1.
  Qed.

  Theorem remove_In : forall (l : list A) (x : A), ~ In x (remove x l).
  Proof.
    intro l; induction l as [|x l IHl]; auto.
    intro y; simpl; destruct (eq_dec y x) as [yeqx | yneqx].
    apply IHl.
    unfold not; intro HF; simpl in HF; destruct HF; auto.
    apply (IHl y); assumption.
  Qed.

  Lemma notin_remove: forall l x, ~ In x l -> remove x l = l.
  Proof.
    intros l x; induction l as [|y l]; simpl; intros Hnin.
    - reflexivity.
    - destruct (eq_dec x y); subst; intuition.
      f_equal; assumption.
  Qed.

  Lemma in_remove: forall l x y, In x (remove y l) -> In x l /\ x <> y.
  Proof.
    intro l; induction l as [|z l IHl]; intros x y Hin.
    - inversion Hin.
    - simpl in Hin.
      destruct (eq_dec y z) as [Heq|Hneq]; subst; split.
      + right; now apply IHl with z.
      + intros Heq; revert Hin; subst; apply remove_In.
      + inversion Hin; subst; [left; reflexivity|right].
        now apply IHl with y.
      + destruct Hin as [Hin|Hin]; subst.
        * now intros Heq; apply Hneq.
        * intros Heq; revert Hin; subst; apply remove_In.
  Qed.

  Lemma in_in_remove : forall l x y, x <> y -> In x l -> In x (remove y l).
  Proof.
    intro l; induction l as [|z l IHl]; simpl; intros x y Hneq Hin.
    - apply Hin.
    - destruct (eq_dec y z); subst.
      + destruct Hin.
        * exfalso; now apply Hneq.
        * now apply IHl.
      + simpl; destruct Hin; [now left|right].
        now apply IHl.
  Qed.

  Lemma remove_remove_comm : forall l x y,
    remove x (remove y l) = remove y (remove x l).
  Proof.
    intro l; induction l as [| z l IHl]; simpl; intros x y.
    - reflexivity.
    - destruct (eq_dec y z); simpl; destruct (eq_dec x z). 
      + (* GOAL #28 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #28: 
Tactic call ran for 0.083 secs (0.034u,0.025s) (failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName4 Tindex_1) (SMTCoqRelName5 Tindex_1)) (= (op_1 SMTCoqRelName5 (op_1 SMTCoqRelName4 op_0)) (op_1 SMTCoqRelName4 (op_1 SMTCoqRelName5 op_0))) ) ).*)
(* RESULT #28: N/A. Quantified. Local lemma. *) try rewrite IHl; auto. 
      + (* GOAL #29 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #29: 
Tactic call ran for 0.064 secs (0.034u,0.008s) (failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName6 Tindex_1) (SMTCoqRelName7 Tindex_1)) (= (op_1 SMTCoqRelName7 (op_1 SMTCoqRelName6 op_0)) (op_1 SMTCoqRelName6 (op_1 SMTCoqRelName7 op_0))) ) ).*)
(* RESULT #29: N/A. Quantified. Local lemma. *)try rewrite IHl; auto. subst; symmetry; apply remove_cons.
      + (* GOAL #30 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #30: 
Tactic call ran for 0.058 secs (0.027u,0.007s) (failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName8 Tindex_1) (SMTCoqRelName9 Tindex_1)) (= (op_1 SMTCoqRelName9 (op_1 SMTCoqRelName8 op_0)) (op_1 SMTCoqRelName8 (op_1 SMTCoqRelName9 op_0))) ) ).*)
(* RESULT #30: N/A. Quantified. Local lemma. *)try rewrite IHl; auto.
      + (* GOAL #31 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #31: 
Tactic call ran for 0.064 secs (0.028u,0.012s) (failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName10 Tindex_1) (SMTCoqRelName11 Tindex_1)) (= (op_1 SMTCoqRelName11 (op_1 SMTCoqRelName10 op_0)) (op_1 SMTCoqRelName10 (op_1 SMTCoqRelName11 op_0))) ) ).
*)
(* RESULT #31: N/A. Quantified. Local lemma. *) try rewrite IHl; auto. simpl; destruct (eq_dec y z); tauto.
  Qed.

  Lemma remove_remove_eq : forall l x, remove x (remove x l) = remove x l.
  Proof. intros l x. (* GOAL #32 *) (* Fail Timeout 20 (time abduce 2). *)
(*assert ((remove x l) = l). { Search (remove _ _ = _). apply notin_remove.
Search (~ In _ _). apply (remove_In l x). } *)
(* OUTPUT #32: 
Tactic call ran for 0.227 secs (0.001u,0.017s) (failure)
The command has indeed failed with message:
cvc5 returned SAT.
The solver cannot prove the goal, but one of the following hypotheses (printed in Prop, but the corresponding Boolean versions also apply) would make it provable:
(remove x l) = l
(remove x (remove x l)) = (remove x l)*)
(* RESULT #32: Failure. Can't poke holes. Asserts goal. *)
rewrite (notin_remove _ _ (remove_In l x)). easy. Qed.

  Lemma remove_length_le : forall l x, length (remove x l) <= length l.
  Proof.
    intro l; induction l as [|y l IHl]; simpl; intros x; trivial.
    destruct (eq_dec x y); simpl.
    - (* GOAL #33 *) (* Fail Timeout 20 (time abduce 1).*)
(* OUTPUT #33: *)
(* RESULT #33: N/A. Quantified. Local lemma. Nat predicate. *) rewrite IHl; constructor; reflexivity.
    - apply (proj1 (Nat.succ_le_mono _ _) (IHl x)).
  Qed.

  Lemma remove_length_lt : forall l x, In x l -> length (remove x l) < length l.
  Proof.
    intro l; induction l as [|y l IHl]; simpl; intros x Hin.
    - contradiction Hin.
    - destruct Hin as [-> | Hin].
      + destruct (eq_dec x x); intuition.
        apply Nat.lt_succ_r, remove_length_le.
      + specialize (IHl _ Hin); destruct (eq_dec x y); simpl; auto.
        now apply Nat.succ_lt_mono in IHl.
  Qed.


  (******************************************)
  (** ** Counting occurrences of an element *)
  (******************************************)

  Fixpoint count_occ (l : list A) (x : A) : nat :=
    match l with
      | [] => 0
      | y :: tl =>
        let n := count_occ tl x in
        if eq_dec y x then S n else n
    end.

  (** Compatibility of count_occ with operations on list *)
  Theorem count_occ_In l x : In x l <-> count_occ l x > 0.
  Proof.
    induction l as [|y l IHl]; simpl.
    - split; [destruct 1 | apply gt_irrefl].
    - destruct eq_dec as [->|Hneq]. 
(* GOAL #34 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #34: *)
(* RESULT #34: N/A. Quantified. Local lemma. Nat predicate. *) rewrite IHl; intuition. 
(* GOAL #35 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #35: *)
(* RESULT #35: N/A. Quantified. Local lemma. Nat predicate. *)
rewrite IHl; intuition.
  Qed.

  Theorem count_occ_not_In l x : ~ In x l <-> count_occ l x = 0.
  Proof.
    (* GOAL #36 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #36: *)
(* RESULT #36: N/A. Nat predicate. *)
    rewrite count_occ_In. unfold gt. now rewrite Nat.nlt_ge, Nat.le_0_r.
  Qed.

  Lemma count_occ_nil x : count_occ [] x = 0.
  Proof.
    reflexivity.
  Qed.

  Theorem count_occ_inv_nil l :
    (forall x:A, count_occ l x = 0) <-> l = [].
  Proof.
    split.
    - induction l as [|x l]; trivial.
      intros H. specialize (H x). simpl in H.
      destruct eq_dec as [_|NEQ]; [discriminate|now elim NEQ].
    - now intros ->.
  Qed.

  Lemma count_occ_cons_eq l x y :
    x = y -> count_occ (x::l) y = S (count_occ l y).
  Proof.
    intros H. simpl. now destruct (eq_dec x y).
  Qed.

  Lemma count_occ_cons_neq l x y :
    x <> y -> count_occ (x::l) y = count_occ l y.
  Proof.
    intros H. simpl. now destruct (eq_dec x y).
  Qed.

End Elts.

(*******************************)
(** * Manipulating whole lists *)
(*******************************)

Section ListOps.

  Variable A : Type.

  (*************************)
  (** ** Reverse           *)
  (*************************)

  Fixpoint rev (l:list A) : list A :=
    match l with
      | [] => []
      | x :: l' => rev l' ++ [x]
    end.

  Lemma rev_app_distr : forall x y:list A, rev (x ++ y) = rev y ++ rev x.
  Proof.
    intro x; induction x as [| a l IHl].
    intro y; destruct y as [| a l].
    simpl.
    auto.

    simpl.
    (* GOAL #37 *) (* + Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #37: The command has indeed failed with message:
Timeout!*)
(* RESULT #37: Failure. Can't poke holes. *)
    rewrite app_nil_r; auto.

    intro y.
    simpl.
    (* GOAL #38 *)  (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #38: 
Tactic call ran for 0.052 secs (0.015u,0.012s) 
(failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName16 Tindex_0)) (= (op_2 (op_1 op_0 SMTCoqRelName16)) (op_1 (op_2 SMTCoqRelName16) (op_2 op_0))) ) ).
*)
(* RESULT #38: N/A. Quantified. Local lemma. *)
    rewrite (IHl y).
    (* GOAL #39 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #39: 
Tactic call ran for 0.058 secs (0.02u,0.013s) 
(failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName17 Tindex_0)) (= (op_2 (op_1 op_0 SMTCoqRelName17)) (op_1 (op_2 SMTCoqRelName17) (op_2 op_0))) ) ).*)
(* RESULT #39: N/A. Quantified. *)
    rewrite app_assoc; trivial.
  Qed.

  Remark rev_unit : forall (l:list A) (a:A), rev (l ++ [a]) = a :: rev l.
  Proof.
    intros l a.
    apply (rev_app_distr l [a]); simpl; auto.
  Qed.

  Lemma rev_involutive : forall l:list A, rev (rev l) = l.
  Proof.
    intro l; induction l as [| a l IHl].
    simpl; auto.

    simpl.
(* GOAL #40 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #40: The command has indeed failed with message:
Timeout! *)
(* RESULT #40: Failure. Can't poke holes. *)
    rewrite (rev_unit (rev l) a). (* verit. admit. admit. *)
(* GOAL #41 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #41: The command has not failed!
Tactic call ran for 0.041 secs (0.011u,0.013s) 
(success)*)
(* RESULT #41: Smt Success. *)
    rewrite IHl; auto.
  Qed.

  Lemma rev_eq_app : forall l l1 l2, rev l = l1 ++ l2 -> l = rev l2 ++ rev l1.
  Proof.
    intros l l1 l2 Heq.
(* GOAL #42 *) 
(* assert (rev (l1 ++ l2) = rev l2 ++ rev l1) by admit.
Fail Timeout 20 (time abduce 4).
assert ((rev (rev l)) = l).
{  Search (rev (rev _) = _ ). apply rev_involutive. } smt. *)
(* OUTPUT #42: Tactic call ran for 0.335 secs (0.023u,0.011s) (failure)
The command has indeed failed with message:
cvc5 returned SAT.
The solver cannot prove the goal, but one of the following hypotheses (printed in Prop, but the corresponding Boolean versions also apply) would make it provable:
((app (A:=A)) l1 l2) = l
(rev l) = l
(rev ((app (A:=A)) l1 l2)) = l
(rev (rev l)) = l *)
(* RESULT #42: Success. Poked holes. *)
    rewrite <- (rev_involutive l), Heq.
    apply rev_app_distr.
  Qed.

  (** Compatibility with other operations *)

  Lemma in_rev : forall l x, In x l <-> In x (rev l).
  Proof.
    intro l; induction l.
    simpl; intuition.
    intros.
    simpl.
    split; intro H; [destruct H|].
    subst.
    apply in_or_app; right; simpl; auto.
    apply in_or_app; left; firstorder.
    destruct (in_app_or _ _ _ H); firstorder.
  Qed.

  Lemma rev_length : forall l, length (rev l) = length l.
  Proof.
    intro l; induction l as [|? l IHl];simpl; auto.
(* GOAL #43 *) 
(* assert (length [a] = 1) by admit.
assert (length l + 1 = S (length l)) by admit.
Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #43: The command has indeed failed with message:
Timeout! *)
(* RESULT #43: Failure. Poked holes. *)
    rewrite app_length.
(* GOAL #44 *) 
(* assert (length [a] = 1) by admit.
assert (length l + 1 = S (length l)) by admit.
Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #44: The command has not failed!
Tactic call ran for 0.052 secs (0.016u,0.008s) (success) *)
(* RESULT #44: Smt Success. Poked holes. *)
    rewrite IHl.
    simpl.
    elim (length l); simpl; auto.
  Qed.

  Lemma rev_nth : forall l d n,  n < length l ->
    nth n (rev l) d = nth (length l - S n) l d.
  Proof.
    intro l; induction l as [|a l IHl].
    intros d n H; inversion H.
    intros ? n H.
    simpl in H.
    simpl (rev (a :: l)).
    simpl (length (a :: l) - S n).
    inversion H.
    + (* GOAL #45 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #45: Tactic call ran for 0.063 secs (0.026u,0.016s) 
(failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName19 Tindex_1) (SMTCoqRelName20 Tindex_0)) (= (op_2 *)
(* RESULT #45: N/A. Quantified. *)
    rewrite <- minus_n_n; simpl.
(* GOAL #46 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #46: 
Tactic call ran for 0.065 secs (0.027u,0.016s) 
(failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName22 Tindex_1) (SMTCoqRelName23 Tindex_0)) (= (op_2 SMTCoqRelName22 (op_1 op_0) SMTCoqRelName23) (op_2 (op_5 (op_3 op_0) (op_4 SMTCoqRelName22)) op_0 SMTCoqRelName23)) ) ).*)
(* RESULT #46: N/A. Quantified. *)
    rewrite <- rev_length.
(* GOAL #47 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #47: Tactic call ran for 0.062 secs (0.025u,0.006s) 
(failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName25 Tindex_1) (SMTCoqRelName26 Tindex_0)) (= (op_2 SMTCoqRelName25 (op_1 op_0) SMTCoqRelName26) (op_2 (op_5 (op_3 op_0) (op_4 SMTCoqRelName25)) op_0 SMTCoqRelName26)) ) ).*)
(* RESULT #47: N/A. Quantified. *)
    rewrite app_nth2; auto.
(* GOAL #48 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #48: 
Tactic call ran for 0.051 secs (0.018u,0.007s) 
(failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName28 Tindex_1) (SMTCoqRelName29 Tindex_0)) (= (op_2 SMTCoqRelName28 (op_1 op_0) SMTCoqRelName29) (op_2 (op_5 (op_3 op_0) (op_4 SMTCoqRelName28)) op_0 SMTCoqRelName29)) ) ).
*)
(* RESULT #48: N/A. Quantified. *)
    rewrite <- minus_n_n; auto.
    + (* GOAL #49 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #49: Tactic call ran for 0.056 secs (0.013u,0.016s) 
(failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName31 Tindex_1) (SMTCoqRelName32 Tindex_0)) (= (op_2 SMTCoqRelName31 (op_1 op_0) SMTCoqRelName32) (op_2 (op_5 (op_3 op_0) (op_4 SMTCoqRelName31)) op_0 SMTCoqRelName32)) ) ).*)
(* RESULT #49: N/A. Quantified.*)
    rewrite app_nth1; auto.
(* GOAL #50 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #50: Tactic call ran for 0.063 secs (0.023u,0.012s) 
(failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName34 Tindex_1) (SMTCoqRelName35 Tindex_0)) (= (op_2 SMTCoqRelName34 (op_1 op_0) SMTCoqRelName35) (op_2 (op_5 (op_3 op_0) (op_4 SMTCoqRelName34)) op_0 SMTCoqRelName35)) ) ).
 *)
(* RESULT #50: N/A. Quantified. *)
    rewrite (minus_plus_simpl_l_reverse (length l) n 1).
    replace (1 + length l) with (S (length l)); auto with arith.
(* GOAL #51 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #51: Tactic call ran for 0.079 secs (0.046u,0.009s) 
(failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName37 Tindex_1) (SMTCoqRelName38 Tindex_0)) (= (op_2 SMTCoqRelName37 (op_1 op_0) SMTCoqRelName38) (op_2 (op_5 (op_3 op_0) (op_4 SMTCoqRelName37)) op_0 SMTCoqRelName38)) ) ). *)
(* RESULT #51: N/A. Quantified. *)
    rewrite <- minus_Sn_m; auto with arith.
    apply IHl ; auto with arith.
(* GOAL #52 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #52: Tactic call ran for 0.039 secs (0.032u,0.006s) 
(failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."*)
(* RESULT #52: N/A. Nat predicate. *)
    rewrite rev_length; auto.
  Qed.


  (**  An alternative tail-recursive definition for reverse *)

  Fixpoint rev_append (l l': list A) : list A :=
    match l with
      | [] => l'
      | a::l => rev_append l (a::l')
    end.

  Definition rev' l : list A := rev_append l [].

  Lemma rev_append_rev : forall l l', rev_append l l' = rev l ++ l'.
  Proof.
    intro l; induction l; simpl; auto; intros.
    (* GOAL #53 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #53: 
Tactic call ran for 0.044 secs (0.013u,0.008s) (failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName0 Tindex_0)) (= (op_1 op_0 SMTCoqRelName0) (op_3 (op_2 op_0) SMTCoqRelName0)) ) ).*)
(* RESULT #53: N/A. Quantified. *)
    rewrite <- app_assoc; firstorder.
  Qed.

  Lemma rev_alt : forall l, rev l = rev_append l [].
  Proof.
    intros. (* GOAL #54 *)
    (* assert (rev l ++ [] = rev l) by admit.
    Fail Timeout 20 (time abduce 2). 
    assert (((app (A:=A)) (rev l) []) = (rev_append l [])).
    { Search (rev _ ++ [] = rev_append _ []). now rewrite rev_append_rev. }
    smt. *)
(* OUTPUT #54:
Tactic call ran for 0.941 secs (0.008u,0.026s) (failure)
The command has indeed failed with message:
cvc5 returned SAT.
The solver cannot prove the goal, but one of the following hypotheses (printed in Prop, but the corresponding Boolean versions also apply) would make it provable:
(rev l) = (rev_append l [])
((app (A:=A)) (rev l) []) = (rev_append l []) *)
(* RESULT #54: Partial. Poked holes. Abduct is symmetry of rewrite. *)
    rewrite rev_append_rev.
(* GOAL #55 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #55: 
Tactic call ran for 0.878 secs (0.003u,0.016s) (failure)
The command has indeed failed with message:
cvc5 returned SAT.
The solver cannot prove the goal, but one of the following hypotheses (printed in Prop, but the corresponding Boolean versions also apply) would make it provable:
((app (A:=A)) (rev l) []) = (rev l)*)
(* assert (((app (A:=A)) (rev l) []) = (rev l)). { Search (_ ++ [] = _).
apply app_nil_r. } smt. *)
(* RESULT #55: Success. *)
    rewrite app_nil_r. trivial.
  Qed.


(*********************************************)
(** Reverse Induction Principle on Lists  *)
(*********************************************)

  Section Reverse_Induction.

    Lemma rev_list_ind : forall P:list A-> Prop,
      P [] ->
      (forall (a:A) (l:list A), P (rev l) -> P (rev (a :: l))) ->
      forall l:list A, P (rev l).
    Proof.
      intros P ? ? l; induction l; auto.
    Qed.

    Theorem rev_ind : forall P:list A -> Prop,
      P [] ->
      (forall (x:A) (l:list A), P l -> P (l ++ [x])) -> forall l:list A, P l.
    Proof.
      intros P H H0 l.
      generalize (rev_involutive l).
      intros E. (* GOAL #56 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #56: 
Tactic call ran for 0.005 secs (0.005u,0.s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."*)
(* RESULT #56: N/A. Non-bool predicate. *)rewrite <- E.
      apply (rev_list_ind P).
      - auto.
      - simpl.
        intros a l0 ?.
        apply (H0 a (rev l0)).
        auto.
    Qed.

  End Reverse_Induction.

  (*************************)
  (** ** Concatenation     *)
  (*************************)

  Fixpoint concat (l : list (list A)) : list A :=
  match l with
  | nil => nil
  | cons x l => x ++ concat l
  end.

  Lemma concat_nil : concat nil = nil.
  Proof.
  reflexivity.
  Qed.

  Lemma concat_cons : forall x l, concat (cons x l) = x ++ concat l.
  Proof.
  reflexivity.
  Qed.

  Lemma concat_app : forall l1 l2, concat (l1 ++ l2) = concat l1 ++ concat l2.
  Proof.
  intros l1; induction l1 as [|x l1 IH]; intros l2; simpl.
  - reflexivity.
  - (* GOAL #57 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #57:
Tactic call ran for 0.034 secs (0.u,0.011s) (failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName1 Tindex_1)) (= (op_2 (op_1 op_0 SMTCoqRelName1)) (op_3 (op_2 op_0) (op_2 SMTCoqRelName1))) ) ). *)
(* RESULT #57: N/A. Quantified. Local lemma. *) rewrite IH; apply app_assoc.
  Qed.

  Lemma in_concat : forall l y,
    In y (concat l) <-> exists x, In x l /\ In y x.
  Proof.
    intro l; induction l as [|a l IHl]; simpl; intro y; split; intros H.
    contradiction.
    destruct H as (x,(H,_)); contradiction.
    destruct (in_app_or _ _ _ H) as [H0|H0].
    exists a; auto.
    destruct (IHl y) as (H1,_); destruct (H1 H0) as (x,(H2,H3)).
    exists x; auto.
    apply in_or_app.
    destruct H as (x,(H0,H1)); destruct H0.
    subst; auto.
    right; destruct (IHl y) as (_,H2); apply H2.
    exists x; auto.
  Qed.


  (***********************************)
  (** ** Decidable equality on lists *)
  (***********************************)

  Hypothesis eq_dec : forall (x y : A), {x = y}+{x <> y}.

  Lemma list_eq_dec : forall l l':list A, {l = l'} + {l <> l'}.
  Proof. decide equality. Defined.

End ListOps.

(***************************************************)
(** * Applying functions to the elements of a list *)
(***************************************************)

(************)
(** ** Map  *)
(************)

Section Map.
  Variables (A : Type) (B : Type).
  Variable f : A -> B.

  Fixpoint map (l:list A) : list B :=
    match l with
      | [] => []
      | a :: t => (f a) :: (map t)
    end.

  Lemma map_cons (x:A)(l:list A) : map (x::l) = (f x) :: (map l).
  Proof.
    reflexivity.
  Qed.

  Lemma in_map :
    forall (l:list A) (x:A), In x l -> In (f x) (map l).
  Proof.
    intro l; induction l; firstorder (subst; auto).
  Qed.

  Lemma in_map_iff : forall l y, In y (map l) <-> exists x, f x = y /\ In x l.
  Proof.
    intro l; induction l; firstorder (subst; auto).
  Qed.

  Lemma map_length : forall l, length (map l) = length l.
  Proof.
    intro l; induction l; simpl; auto.
  Qed.

  Lemma map_nth : forall l d n,
    nth n (map l) (f d) = f (nth n l d).
  Proof.
    intro l; induction l; simpl map; intros d n; destruct n; firstorder.
  Qed.

  Lemma map_nth_error : forall n l d,
    nth_error l n = Some d -> nth_error (map l) n = Some (f d).
  Proof.
    intro n; induction n; intros [ | ] ? Heq; simpl in *; inversion Heq; auto.
  Qed.

  Lemma map_app : forall l l',
    map (l++l') = (map l)++(map l').
  Proof.
    intro l; induction l as [|a l IHl]; simpl; auto.
    intros. (* GOAL #58 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #58: 
Tactic call ran for 0.035 secs (0.003u,0.009s) (failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName2 Tindex_1)) (= (op_2 (op_1 op_0 SMTCoqRelName2)) (op_3 (op_2 op_0) (op_2 SMTCoqRelName2))) ) ).
*)
(* RESULT #58: N/A. Quantified. Local lemma. *)
rewrite IHl; auto.
  Qed.

  Lemma map_last : forall l a,
    map (l ++ [a]) = (map l) ++ [f a].
  Proof.
    intro l; induction l as [|a l IHl]; intros; [ reflexivity | ].
    simpl. (* GOAL #59 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #59: 
Tactic call ran for 0.094 secs (0.01u,0.004s) (failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName0 Tindex_2)) (= (op_4 (op_3 op_0 (op_2 SMTCoqRelName0 op_1))) (op_8 (op_4 op_0) (op_7 (op_5 SMTCoqRelName0) op_6))) ) ). *)
(* RESULT #59: N/A. Quantified. Local lemma.*) rewrite IHl; reflexivity.
  Qed.

  Lemma map_rev : forall l, map (rev l) = rev (map l).
  Proof.
    intro l; induction l as [|a l IHl]; simpl; auto.
    (* GOAL #60 *)
    (* assert (map [a] = [f a]) by admit. 
       Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #60: 
The command has indeed failed with message:
Timeout! *)
(* RESULT #60: Failure. Poked holes. *)
    rewrite map_app.
(* GOAL #61 *) 
(* assert (map [a] = [f a]) by admit. 
Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #61:
The command has not failed!
Tactic call ran for 0.034 secs (0.011u,0.007s) (success) *)
(* RESULT #61: Smt Success. Poked holes. *)
    rewrite IHl; auto.
  Qed.

  Lemma map_eq_nil : forall l, map l = [] -> l = [].
  Proof.
    intro l; destruct l; simpl; reflexivity || discriminate.
  Qed.

  Lemma map_eq_cons : forall l l' b,
    map l = b :: l' -> exists a tl, l = a :: tl /\ f a = b /\ map tl = l'.
  Proof.
    intros l l' b Heq.
    destruct l as [|a l]; inversion_clear Heq.
    exists a, l; repeat split.
  Qed.

  Lemma map_eq_app  : forall l l1 l2,
    map l = l1 ++ l2 -> exists l1' l2', l = l1' ++ l2' /\ map l1' = l1 /\ map l2' = l2.
  Proof.
    intro l; induction l as [|a l IHl]; simpl; intros l1 l2 Heq.
    - symmetry in Heq; apply app_eq_nil in Heq; destruct Heq; subst.
      exists nil, nil; repeat split.
    - destruct l1; simpl in Heq; inversion Heq as [[Heq2 Htl]].
      + exists nil, (a :: l); repeat split.
      + destruct (IHl _ _ Htl) as (l1' & l2' & ? & ? & ?); subst.
        exists (a :: l1'), l2'; repeat split.
  Qed.

  (** [map] and count of occurrences *)

  Hypothesis decA: forall x1 x2 : A, {x1 = x2} + {x1 <> x2}.
  Hypothesis decB: forall y1 y2 : B, {y1 = y2} + {y1 <> y2}.
  Hypothesis Hfinjective: forall x1 x2: A, (f x1) = (f x2) -> x1 = x2.

  Theorem count_occ_map x l:
    count_occ decA l x = count_occ decB (map l) (f x).
  Proof.
    revert x. induction l as [| a l' Hrec]; intro x; simpl.
    - reflexivity.
    - specialize (Hrec x).
      destruct (decA a x) as [H1|H1], (decB (f a) (f x)) as [H2|H2].
      + 
(* GOAL #62 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #62: 
Tactic call ran for 0.063 secs (0.042u,0.001s) (failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName4 Tindex_1) (SMTCoqRelName5 Tindex_1)) (or (not (= (op_0 SMTCoqRelName5) (op_0 SMTCoqRelName4))) (= SMTCoqRelName4 SMTCoqRelName5)) ) ).
*)
(* RESULT #62: N/A. Quantified. Local lemma. *)rewrite Hrec. reflexivity.
      + contradiction H2. 
(* GOAL #63 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #63: 

Tactic call ran for 0.079 secs (0.046u,0.012s) (failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName6 Tindex_1) (SMTCoqRelName7 Tindex_1)) (or (not (= (op_0 SMTCoqRelName7) (op_0 SMTCoqRelName6))) (= SMTCoqRelName6 SMTCoqRelName7)) ) ).
*)
(* RESULT #63: N/A. Quantified. Local lemma. *) rewrite H1. reflexivity.
      + specialize (Hfinjective H2). contradiction H1.
      + assumption.
  Qed.

  (** [flat_map] *)

  Definition flat_map (f:A -> list B) :=
    fix flat_map (l:list A) : list B :=
    match l with
      | nil => nil
      | cons x t => (f x)++(flat_map t)
    end.

  Lemma flat_map_app : forall f l1 l2,
    flat_map f (l1 ++ l2) = flat_map f l1 ++ flat_map f l2.
  Proof.
    intros F l1 l2.
    induction l1 as [|? ? IHl1]; [ reflexivity | simpl ].
(* GOAL #64 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #64: 
Tactic call ran for 0.038 secs (0.038u,0.s) (failure)
The command has indeed failed with message:
Anomaly "Uncaught exception Invalid_argument("index out of bounds")."
Please report at http://coq.inria.fr/bugs/. *)
(* RESULT #64: N/A. Out of bounds. Local lemma. *)
    rewrite IHl1.
(* GOAL #65 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #65:

Tactic call ran for 0.053 secs (0.04u,0.012s) (failure)
The command has indeed failed with message:
Anomaly "Uncaught exception Invalid_argument("index out of bounds")."
Please report at http://coq.inria.fr/bugs/.
 *)
(* RESULT #65: N/A. Out of bounds. *)
rewrite app_assoc. reflexivity.
  Qed.

  Lemma in_flat_map : forall (f:A->list B)(l:list A)(y:B),
    In y (flat_map f l) <-> exists x, In x l /\ In y (f x).
  Proof.
    clear f Hfinjective.
    intros f l; induction l as [|a l IHl]; simpl; intros y; split; intros H.
    contradiction.
    destruct H as (x,(H,_)); contradiction.
    destruct (in_app_or _ _ _ H) as [H0|H0].
    exists a; auto.
    destruct (IHl y) as (H1,_); destruct (H1 H0) as (x,(H2,H3)).
    exists x; auto.
    apply in_or_app.
    destruct H as (x,(H0,H1)); destruct H0.
    subst; auto.
    right; destruct (IHl y) as (_,H2); apply H2.
    exists x; auto.
  Qed.

End Map.

Lemma flat_map_concat_map : forall A B (f : A -> list B) l,
  flat_map f l = concat (map f l).
Proof.
intros A B f l; induction l as [|x l IH]; simpl.
- reflexivity.
- (* GOAL #67 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #67: 

Tactic call ran for 0.022 secs (0.022u,0.s) (failure)
The command has indeed failed with message:
Anomaly "Uncaught exception Invalid_argument("index out of bounds")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #67: N/A. Out of bounds. Local lemma. *)rewrite IH; reflexivity.
Qed.

Lemma concat_map : forall A B (f : A -> B) l, map f (concat l) = concat (map (map f) l).
Proof.
intros A B f l; induction l as [|x l IH]; simpl.
- reflexivity.
- (* GOAL #68 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #68: 
Tactic call ran for 0.054 secs (0.023u,0.005s) (failure)
The command has indeed failed with message:
Solver error: (error argument type is not a subtype of the function's argument type:
argument:  (op_3 op_0)
has type:  (-> Tindex_3 Tindex_0)
not subtype: Tindex_0
in term : (op_4 (as (op_3 op_0) Tindex_0) op_1) ).
 *)
(* RESULT #68: N/A. Not subtype. *)
rewrite map_app.
(* GOAL #69 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #69: 
Tactic call ran for 0.046 secs (0.025u,0.001s) (failure)
The command has indeed failed with message:
Solver error: (error argument type is not a subtype of the function's argument type:
argument:  (op_3 op_0)
has type:  (-> Tindex_3 Tindex_0)
not subtype: Tindex_0
in term : (op_4 (as (op_3 op_0) Tindex_0) op_1) ). *)
(* RESULT #69: N/A. Not subtype. Local lemma. *)
rewrite IH; reflexivity.
Qed.

Lemma remove_concat A (eq_dec : forall x y : A, {x = y}+{x <> y}) : forall l x,
  remove eq_dec x (concat l) = flat_map (remove eq_dec x) l.
Proof.
  intros l x; induction l as [|? ? IHl]; [ reflexivity | simpl ].
(* GOAL #70 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #70: 
Tactic call ran for 0.037 secs (0.004u,0.01s) (failure)
The command has indeed failed with message:
Solver error: (error argument type is not a subtype of the function's argument type:
argument:  ((op_4 op_0) op_1)
has type:  (-> Tindex_0 Tindex_0)
not subtype: Tindex_0
in term : (op_5 (as ((op_4 op_0) op_1) Tindex_0) op_2) ).
*)
(* RESULT #70: N/A. Not subtype. *)
  rewrite remove_app. 
(* GOAL #71 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #71: 
Tactic call ran for 0.037 secs (0.01u,0.004s) (failure)
The command has indeed failed with message:
Solver error: (error argument type is not a subtype of the function's argument type:
argument:  ((op_4 op_0) op_1)
has type:  (-> Tindex_0 Tindex_0)
not subtype: Tindex_0
in term : (op_5 (as ((op_4 op_0) op_1) Tindex_0) op_2) ).
*)
(* RESULT #71: N/A. Not subtype. Local lemma. *)rewrite IHl; reflexivity.
Qed.

Lemma map_id : forall (A :Type) (l : list A),
  map (fun x => x) l = l.
Proof.
  intros A l; induction l as [|? ? IHl]; simpl; auto. (* verit. admit. admit. *)
  (* GOAL #72 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #72: 
The command has not failed!
Tactic call ran for 0.042 secs (0.016u,0.01s) (success)
*)
(* RESULT #72: Smt Success. Local lemma. *)rewrite IHl; auto.
Qed.

Lemma map_map : forall (A B C:Type)(f:A->B)(g:B->C) l,
  map g (map f l) = map (fun x => g (f x)) l.
Proof.
  intros A B C f g l; induction l as [|? ? IHl]; simpl; auto.
  (* GOAL #73 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #73: 
Tactic call ran for 0.007 secs (0.007u,0.s) (failure)
The command has indeed failed with message:
Anomaly "Uncaught exception Invalid_argument("index out of bounds")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #73: N/A. Out of bounds. Local lemma. *)rewrite IHl; auto.
Qed.

Lemma map_ext_in :
  forall (A B : Type)(f g:A->B) l, (forall a, In a l -> f a = g a) -> map f l = map g l.
Proof.
  intros A B f g l; induction l as [|? ? IHl]; simpl; auto.
  intros H. (* GOAL #74 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #74: 
Discarding the following lemma (unsupported): ((forall a : A, In a l -> f a = g a) -> map f l = map g l)
[Lemma,SMTCoq plugin]
Tactic call ran for 0.066 secs (0.045u,0.002s) (failure)
The command has indeed failed with message:
Solver error: (error argument type is not a subtype of the function's argument type:
argument:  op_1
has type:  (-> Tindex_2 Tindex_1)
not subtype: Tindex_1
in term : (op_4 (as op_1 Tindex_1) op_3) ).
*)
(* RESULT #74: N/A. Not subtype. Local lemma. *)rewrite H by intuition.
(* GOAL #75 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #75: 
Discarding the following lemma (unsupported): ((forall a : A, In a l -> f a = g a) -> map f l = map g l)
[Lemma,SMTCoq plugin]
Tactic call ran for 0.08 secs (0.054u,0.005s) (failure)
The command has indeed failed with message:
Solver error: (error argument type is not a subtype of the function's argument type:
argument:  op_1
has type:  (-> Tindex_2 Tindex_1)
not subtype: Tindex_1
in term : (op_4 (as op_1 Tindex_1) op_3) ).
*)
(* RESULT #75: N/A. Not subtype. Local lemma. *) rewrite IHl. auto. auto.
Qed.

Lemma ext_in_map :
  forall (A B : Type)(f g:A->B) l, map f l = map g l -> forall a, In a l -> f a = g a.
Proof. intros A B f g l; induction l; intros [=] ? []; subst; auto. Qed.

Arguments ext_in_map [A B f g l].

Lemma map_ext_in_iff :
   forall (A B : Type)(f g:A->B) l, map f l = map g l <-> forall a, In a l -> f a = g a.
Proof. split; [apply ext_in_map | apply map_ext_in]. Qed.

Arguments map_ext_in_iff {A B f g l}.

Lemma map_ext :
  forall (A B : Type)(f g:A->B), (forall a, f a = g a) -> forall l, map f l = map g l.
Proof.
  intros; apply map_ext_in; auto.
Qed.

Lemma flat_map_ext : forall (A B : Type)(f g : A -> list B),
  (forall a, f a = g a) -> forall l, flat_map f l = flat_map g l.
Proof.
  intros A B f g Hext l. (* GOAL #76 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #76: 
Tactic call ran for 0.041 secs (0.007u,0.008s) (failure)
The command has indeed failed with message:
Solver error: (error argument type is not a subtype of the function's argument type:
argument:  op_1
has type:  (-> Tindex_1 Tindex_0)
not subtype: Tindex_0
in term : (op_3 (as op_1 Tindex_0) op_2) ).
*)
(* RESULT #76: N/A. Not subtype. *)rewrite flat_map_concat_map. 
(* GOAL #77 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #77: 
Tactic call ran for 0.041 secs (0.007u,0.008s) (failure)
The command has indeed failed with message:
Solver error: (error argument type is not a subtype of the function's argument type:
argument:  op_1
has type:  (-> Tindex_1 Tindex_0)
not subtype: Tindex_0
in term : (op_5 (as op_1 Tindex_0) op_2) ).
*)
(* RESULT #77: N/A. Not subtype. *)
  rewrite flat_map_concat_map. 
(* GOAL #78 *) (* F ail Timeout 20 (time abduce 1). *)
(* OUTPUT #78: 
Tactic call ran for 0.044 secs (0.013u,0.002s) (failure)
The command has indeed failed with message:
Solver error: (error argument type is not a subtype of the function's argument type:
argument:  op_1
has type:  (-> Tindex_1 Tindex_0)
not subtype: Tindex_0
in term : (op_3 (as op_1 Tindex_0) op_2) ).
*)
(* RESULT #78: N/A. Not subtype. *)now rewrite (map_ext _ g).
Qed.

Lemma nth_nth_nth_map A : forall (l : list A) n d ln dn, n < length ln \/ length l <= dn ->
  nth (nth n ln dn) l d = nth n (map (fun x => nth x l d) ln) d.
Proof.
  intros l n d ln dn; revert n; induction ln as [|? ? IHln]; intros n Hlen.
  - destruct Hlen as [Hlen|Hlen].
    + inversion Hlen.
    + (* GOAL #79 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #79: 
Discarding the following lemma (unsupported): (length l <= dn : Prop)
[Lemma,SMTCoq plugin]
Tactic call ran for 4.667 secs (0.007u,0.019s) (failure)
The command has indeed failed with message:
cvc5 returned SAT.
The solver cannot prove the goal, but one of the following hypotheses (printed in Prop, but the corresponding Boolean versions also apply) would make it provable:
((nth (A:=A)) n ((map (A:=nat) (B:=A)) (fun x : nat => nth x l d) []) d) = ((nth (A:=A)) ((nth (A:=nat)) n [] dn) l d)
*)
(* RESULT #79: Failure. Can't poke holes. *)now rewrite nth_overflow; destruct n.
  - destruct n; simpl; [ reflexivity | apply IHln ].
    destruct Hlen; [ left; apply lt_S_n | right ]; assumption.
Qed.


(************************************)
(** Left-to-right iterator on lists *)
(************************************)

Section Fold_Left_Recursor.
  Variables (A : Type) (B : Type).
  Variable f : A -> B -> A.

  Fixpoint fold_left (l:list B) (a0:A) : A :=
    match l with
      | nil => a0
      | cons b t => fold_left t (f a0 b)
    end.

  Lemma fold_left_app : forall (l l':list B)(i:A),
    fold_left (l++l') i = fold_left l' (fold_left l i).
  Proof.
    intro l; induction l.
    simpl; auto.
    intros.
    simpl.
    auto.
  Qed.

End Fold_Left_Recursor.

Lemma fold_left_length :
  forall (A:Type)(l:list A), fold_left (fun x _ => S x) l 0 = length l.
Proof.
  intros A l.
  enough (H : forall n, fold_left (fun x _ => S x) l n = n + length l) by exact (H 0).
  induction l as [|? ? IHl]; simpl; auto.
  intros. (* GOAL #80 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #80: 
Tactic call ran for 0.047 secs (0.009u,0.008s) (failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName1 Tindex_0)) (= (op_2 op_0 op_1 SMTCoqRelName1) (op_4 SMTCoqRelName1 (op_3 op_1))) ) ).*)
(* RESULT #80: N/A. Quantified. Local lemma. *) rewrite IHl.
  simpl; auto with arith.
Qed.

(************************************)
(** Right-to-left iterator on lists *)
(************************************)

Section Fold_Right_Recursor.
  Variables (A : Type) (B : Type).
  Variable f : B -> A -> A.
  Variable a0 : A.

  Fixpoint fold_right (l:list B) : A :=
    match l with
      | nil => a0
      | cons b t => f b (fold_right t)
    end.

End Fold_Right_Recursor.

  Lemma fold_right_app : forall (A B:Type)(f:A->B->B) l l' i,
    fold_right f i (l++l') = fold_right f (fold_right f i l') l.
  Proof.
    intros A B f l; induction l.
    simpl; auto.
    simpl; intros.
    f_equal; auto.
  Qed.

  Lemma fold_left_rev_right : forall (A B:Type)(f:A->B->B) l i,
    fold_right f i (rev l) = fold_left (fun x y => f y x) l i.
  Proof.
    intros A B f l; induction l.
    simpl; auto.
    intros.
    simpl. (* GOAL #81 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #81: Tactic call ran for 0.019 secs (0.019u,0.s) (failure)
The command has indeed failed with message:
Anomaly "Uncaught exception Invalid_argument("index out of bounds")."
Please report at http://coq.inria.fr/bugs/. *)
(* RESULT #81: N/A. Out of bounds. *)
    rewrite fold_right_app; simpl; auto.
  Qed.

  Theorem fold_symmetric :
    forall (A : Type) (f : A -> A -> A),
    (forall x y z : A, f x (f y z) = f (f x y) z) ->
    forall (a0 : A), (forall y : A, f a0 y = f y a0) ->
    forall (l : list A), fold_left f l a0 = fold_right f a0 l.
  Proof.
    intros A f assoc a0 comma0 l.
    induction l as [ | a1 l IHl]; [ simpl; reflexivity | ].
    simpl. (* GOAL #82 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #82: Tactic call ran for 0.082 secs (0.019u,0.016s) (failure)
The command has indeed failed with message:
Solver error: (error argument type is not a subtype of the function's argument type:
argument:  op_0
has type:  (-> Tindex_0 Tindex_0 Tindex_0)
not subtype: Tindex_0
in term : (op_4 (as op_0 Tindex_0) op_2 op_1) ).*)
(* RESULT #82: N/A. Not subtype. Local lemma. *)rewrite <- IHl. clear IHl. revert a1.
    induction l as [|? ? IHl]; [ auto | ].
    simpl. intro. (* GOAL #83 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #83: Tactic call ran for 0.07 secs (0.022u,0.02s) (failure)
The command has indeed failed with message:
Solver error: (error argument type is not a subtype of the function's argument type:
argument:  op_0
has type:  (-> Tindex_0 Tindex_0 Tindex_0)
not subtype: Tindex_0
in term : (op_3 (as op_0 Tindex_0) op_1 op_2) ).*)
(* RESULT #83: N/A. Not subtype. Local lemma. *)rewrite <- assoc.
(* GOAL #84 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #84: 
Tactic call ran for 0.061 secs (0.011u,0.023s) (failure)
The command has indeed failed with message:
Solver error: (error argument type is not a subtype of the function's argument type:
argument:  op_0
has type:  (-> Tindex_0 Tindex_0 Tindex_0)
not subtype: Tindex_0
in term : (op_3 (as op_0 Tindex_0) op_1 op_2) ).*)
(* RESULT #84: N/A. Not subtype. Local lemma. *)
rewrite IHl. (* GOAL #85 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #85: 
Tactic call ran for 0.061 secs (0.029u,0.008s) (failure)
The command has indeed failed with message:
Solver error: (error argument type is not a subtype of the function's argument type:
argument:  op_0
has type:  (-> Tindex_0 Tindex_0 Tindex_0)
not subtype: Tindex_0
in term : (op_3 (as op_0 Tindex_0) op_1 op_2) ).
*)
(* RESULT #85: N/A. Not subtype. Local lemma. *)
rewrite IHl. auto.
  Qed.

  (** [(list_power x y)] is [y^x], or the set of sequences of elts of [y]
      indexed by elts of [x], sorted in lexicographic order. *)

  Fixpoint list_power (A B:Type)(l:list A) (l':list B) :
    list (list (A * B)) :=
    match l with
      | nil => cons nil nil
      | cons x t =>
	flat_map (fun f:list (A * B) => map (fun y:B => cons (x, y) f) l')
        (list_power t l')
    end.


  (*************************************)
  (** ** Boolean operations over lists *)
  (*************************************)

  Section Bool.
    Variable A : Type.
    Variable f : A -> bool.

  (** find whether a boolean function can be satisfied by an
       elements of the list. *)

    Fixpoint existsb (l:list A) : bool :=
      match l with
      | nil => false
      | a::l => f a || existsb l
      end.

    Lemma existsb_exists :
      forall l, existsb l = true <-> exists x, In x l /\ f x = true.
    Proof.
      intro l; induction l as [ | a m IH ]; split; simpl.
      - easy.
      - intros [x [[]]].
      - (* GOAL #86 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #86: 
Tactic call ran for 0.014 secs (0.014u,0.s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #86: N/A. Quantified. Non-bool predicate. *)rewrite orb_true_iff; intros [ H | H ].
        + exists a; auto.
        + (* GOAL #87 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #87: 
Tactic call ran for 0.012 secs (0.008u,0.004s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.*)
(* RESULT #87: N/A. Quantified. Non-bool predicate. *)rewrite IH in H; destruct H as [ x [ Hxm Hfx ] ].
          exists x; auto.
      - intros [ x [ [ Hax | Hxm ] Hfx ] ].
        +  (* verit. admit. *) (* GOAL #88 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #88: The command has not failed!
Discarding the following lemma (unsupported): (existsb m = true <-> (exists x : A, In x m /\ f x = true) : Prop)
[Lemma,SMTCoq plugin]
Tactic call ran for 0.052 secs (0.013u,0.02s) (success)*)
(* RESULT #88: Smt Success. *)rewrite Hax. (* verit. admit. *)
(* GOAL #89 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #89: 
Discarding the following lemma (unsupported): (existsb m = true <-> (exists x : A, In x m /\ f x = true) : Prop)
[Lemma,SMTCoq plugin]
The command has not failed!
Tactic call ran for 0.049 secs (0.014u,0.016s) (success)*)
(* RESULT #89: Smt Success. *)rewrite Hfx. easy.
        + destruct IH as [ _ -> ]; eauto with bool.
    Qed.

    Lemma existsb_nth : forall l n d, n < length l ->
      existsb l = false -> f (nth n l d) = false.
    Proof.
      intro l; induction l as [|? ? IHl].
      inversion 1.
      simpl; intros n ? ? H0.
      destruct (orb_false_elim _ _ H0); clear H0; auto.
      destruct n ; auto.
(* GOAL #90 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #90: 
Discarding the following lemma (unsupported): (S n < S (length l) : Prop)
[Lemma,SMTCoq plugin]
Tactic call ran for 0.084 secs (0.049u,0.012s) (failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName23 Tindex_2) (SMTCoqRelName24 Tindex_1)) (not (op_3 (op_2 SMTCoqRelName24 op_0 SMTCoqRelName23))) ) ).
*)
(* RESULT #90: N/A. Quantified. Local lemma. *)
      rewrite IHl; auto with arith.
    Qed.

    Lemma existsb_app : forall l1 l2,
      existsb (l1++l2) = existsb l1 || existsb l2.
    Proof.
      intro l1; induction l1 as [|a ? ?]; intros l2; simpl.
        solve[auto].
      case (f a); simpl; solve[auto].
    Qed.

  (** find whether a boolean function is satisfied by
    all the elements of a list. *)

    Fixpoint forallb (l:list A) : bool :=
      match l with
      | nil => true
      | a::l => f a && forallb l
      end.

    Lemma forallb_forall :
      forall l, forallb l = true <-> (forall x, In x l -> f x = true).
    Proof.
      intro l; induction l as [|a l IHl]; simpl; [ tauto | split; intro H ].
      + destruct (andb_prop _ _ H); intros a' [?|?].
        - congruence.
        - apply IHl; assumption.
      + apply andb_true_intro; split.
        - apply H; left; reflexivity.
        - apply IHl; intros; apply H; right; assumption.
    Qed.

    Lemma forallb_app :
      forall l1 l2, forallb (l1++l2) = forallb l1 && forallb l2.
    Proof.
      intro l1; induction l1 as [|a ? ?]; simpl.
        solve[auto].
      case (f a); simpl; solve[auto].
    Qed.

  (** [filter] *)

    Fixpoint filter (l:list A) : list A :=
      match l with
      | nil => nil
      | x :: l => if f x then x::(filter l) else filter l
      end.

    Lemma filter_In : forall x l, In x (filter l) <-> In x l /\ f x = true.
    Proof.
      intros x l; induction l as [|a ? ?]; simpl.
      intuition.
      intros.
      case_eq (f a); intros; simpl; intuition congruence.
    Qed.

    Lemma filter_app (l l':list A) :
      filter (l ++ l') = filter l ++ filter l'.
    Proof.
      induction l as [|x l IH]; simpl; trivial.
      destruct (f x). simpl. (* verit. admit. admit.*) (* GOAL #91 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #91: The command has not failed!
Tactic call ran for 0.045 secs (0.011u,0.017s) (success) *)
(* RESULT #91: Smt Success. *) now rewrite IH.
      simpl. (* smt. *) (* GOAL #92 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #92: 
The command has not failed!
Tactic call ran for 0.039 secs (0.011u,0.012s) (success)*)
(* RESULT #92: Smt Success. Local lemma. *)now rewrite IH.
    Qed.

    Lemma concat_filter_map : forall (l : list (list A)),
      concat (map filter l) = filter (concat l).
    Proof.
      intro l; induction l as [| v l IHl]; [auto|].
      simpl. (* GOAL #93 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #93: 
Tactic call ran for 0.018 secs (0.015u,0.003s) (failure)
The command has indeed failed with message:
Anomaly "Uncaught exception Invalid_argument("index out of bounds")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #93: N/A. Out of bounds. Local lemma. *)rewrite IHl. 
(* GOAL #94 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #94: 
Tactic call ran for 0.017 secs (0.013u,0.004s) (failure)
The command has indeed failed with message:
Anomaly "Uncaught exception Invalid_argument("index out of bounds")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #94: N/A. Out of bounds. *)rewrite filter_app. reflexivity.
    Qed.

  (** [find] *)

    Fixpoint find (l:list A) : option A :=
      match l with
      | nil => None
      | x :: tl => if f x then Some x else find tl
      end.

    Lemma find_some l x : find l = Some x -> In x l /\ f x = true.
    Proof.
     induction l as [|a l IH]; simpl; [easy| ].
     case_eq (f a); intros Ha Eq.
     * injection Eq as [= ->]; auto.
     * destruct (IH Eq); auto.
    Qed.

    Lemma find_none l : find l = None -> forall x, In x l -> f x = false.
    Proof.
     induction l as [|a l IH]; simpl; [easy|].
     case_eq (f a); intros Ha Eq x IN; [easy|].
     destruct IN as [<-|IN]; auto.
    Qed.

  (** [partition] *)

    Fixpoint partition (l:list A) : list A * list A :=
      match l with
      | nil => (nil, nil)
      | x :: tl => let (g,d) := partition tl in
                   if f x then (x::g,d) else (g,x::d)
      end.

  Theorem partition_cons1 a l l1 l2:
    partition l = (l1, l2) ->
    f a = true ->
    partition (a::l) = (a::l1, l2).
  Proof.
    simpl. now intros -> ->.
  Qed.

  Theorem partition_cons2 a l l1 l2:
    partition l = (l1, l2) ->
    f a=false ->
    partition (a::l) = (l1, a::l2).
  Proof.
    simpl. now intros -> ->.
  Qed.

  Theorem partition_length l l1 l2:
    partition l = (l1, l2) ->
    length l = length l1 + length l2.
  Proof.
    revert l1 l2. induction l as [ | a l' Hrec]; intros l1 l2.
    - now intros [= <- <- ].
    - simpl. destruct (f a), (partition l') as (left, right).
      intros [= <- <- ]; simpl. (* GOAL #95 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #95: 
Tactic call ran for 0.081 secs (0.039u,0.016s) (failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName25 Tindex_1) (SMTCoqRelName26 Tindex_1)) (or (not (= (op_2 op_0 op_1) (op_2 SMTCoqRelName26 SMTCoqRelName25))) (= (op_4 op_3) (op_5 (op_4 SMTCoqRelName26) (op_4 SMTCoqRelName25)))) ) ).*)
(* RESULT #95: N/A. Quantified. Local lemma. *)rewrite (Hrec left right); auto.
      intros [= <- <- ]; simpl. (* GOAL #96 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #96: 
Tactic call ran for 0.085 secs (0.046u,0.019s) (failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName27 Tindex_1) (SMTCoqRelName28 Tindex_1)) (or (not (= (op_2 op_0 op_1) (op_2 SMTCoqRelName28 SMTCoqRelName27))) (= (op_4 op_3) (op_5 (op_4 SMTCoqRelName28) (op_4 SMTCoqRelName27)))) ) ).
*)
(* RESULT #96: N/A. Quantified. Local lemma.*)rewrite (Hrec left right); auto.
  Qed.

  Theorem partition_inv_nil (l : list A):
    partition l = ([], []) <-> l = [].
  Proof.
    split.
    - destruct l as [|a l'].
      * intuition.
      * simpl. destruct (f a), (partition l'); now intros [= -> ->].
    - now intros ->.
  Qed.

  Theorem elements_in_partition l l1 l2:
    partition l = (l1, l2) ->
    forall x:A, In x l <-> In x l1 \/ In x l2.
  Proof.
    revert l1 l2. induction l as [| a l' Hrec]; simpl; intros l1 l2 Eq x.
    - injection Eq as [= <- <-]. tauto.
    - destruct (partition l') as (left, right).
      specialize (Hrec left right eq_refl x).
      destruct (f a); injection Eq as [= <- <-]; simpl; tauto.
  Qed.

  End Bool.


  (*******************************)
  (** ** Further filtering facts *)
  (*******************************)

  Section Filtering.
    Variables (A : Type).

    Lemma filter_map : forall (f g : A -> bool) (l : list A),
      filter f l = filter g l <-> map f l = map g l.
    Proof.
      intros f g l; induction l as [| a l IHl]; [firstorder|].
      simpl. destruct (f a) eqn:Hfa; destruct (g a) eqn:Hga; split; intros H.
      - inversion H as [H1]. apply IHl in H1. 
(* GOAL #97 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #97: Discarding the following lemma (unsupported): (filter f l = filter g l <-> map f l = map g l)
[Lemma,SMTCoq plugin]
Tactic call ran for 0.015 secs (0.015u,0.s) (failure)
The command has indeed failed with message:
Anomaly "Uncaught exception Invalid_argument("index out of bounds")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #97: N/A. Out of bounds. Local lemma. *)rewrite H1. reflexivity.
      - inversion H as [H1]. apply IHl in H1.
(* GOAL #98 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #98: 
Discarding the following lemma (unsupported): (filter f l = filter g l <-> map f l = map g l)
[Lemma,SMTCoq plugin]
Tactic call ran for 0.027 secs (0.027u,0.s) (failure)
The command has indeed failed with message:
Anomaly "Uncaught exception Invalid_argument("index out of bounds")."
Please report at http://coq.inria.fr/bugs/.*)
(* RESULT #98: N/A. Out of bounds. Local lemma. *) rewrite H1. reflexivity.
      - assert (Ha : In a (filter g l)). { 
(* GOAL #99 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #99: Tactic call ran for 0.036 secs (0.036u,0.s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.*)
(* RESULT #99: N/A. Non-bool predicate. Local lemma. *)rewrite <- H. apply in_eq. }
        apply filter_In in Ha. destruct Ha as [_ Hga']. 
(* GOAL #100 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #100: 
Discarding the following lemma (unsupported): (filter f l = filter g l <-> map f l = map g l)
[Lemma,SMTCoq plugin]
Tactic call ran for 0.021 secs (0.021u,0.s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Atom op_1 (aka g) is not of the expected type")."
Please report at http://coq.inria.fr/bugs/.*)
(* RESULT #100: N/A. Atom not of expected type. Rewrite in hyp. *)
rewrite Hga in Hga'. inversion Hga'.
      - inversion H.
      - assert (Ha : In a (filter f l)). { 
(* GOAL #101 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #101: 
Tactic call ran for 0.03 secs (0.026u,0.004s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.*)
(* RESULT #101: N/A. Non-bool predicate. Local lemma. *)rewrite H. apply in_eq. }
        apply filter_In in Ha. destruct Ha as [_ Hfa']. 
(* GOAL #102 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #102: Discarding the following lemma (unsupported): (filter f l = filter g l <-> map f l = map g l)
[Lemma,SMTCoq plugin]
Tactic call ran for 0.017 secs (0.017u,0.s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Atom op_4 (aka g) is not of the expected type")."
Please report at http://coq.inria.fr/bugs/.*)
(* RESULT #102: N/A. Atom not of expected type. Rewrite in hyp. *)rewrite Hfa in Hfa'. inversion Hfa'.
      - inversion H.
      - (* GOAL #103 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #103: 
Discarding the following lemma (unsupported): (filter f l = filter g l <-> map f l = map g l)
[Lemma,SMTCoq plugin]
Tactic call ran for 0.024 secs (0.024u,0.s) (failure)
The command has indeed failed with message:
Anomaly "Uncaught exception Invalid_argument("index out of bounds")."
Please report at http://coq.inria.fr/bugs/.*)
(* RESULT #103: N/A. Out of bounds. Rewrite in hyp. *)rewrite IHl in H.
(* GOAL #104 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #104: 
Discarding the following lemma (unsupported): (filter f l = filter g l <-> map f l = map g l)
[Lemma,SMTCoq plugin]
Tactic call ran for 0.025 secs (0.025u,0.s) (failure)
The command has indeed failed with message:
Anomaly "Uncaught exception Invalid_argument("index out of bounds")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #104: N/A. Out of bounds. Local lemma. *) rewrite H. reflexivity.
      - inversion H. apply IHl. assumption.
    Qed.

    Lemma filter_ext_in : forall (f g : A -> bool) (l : list A),
      (forall a, In a l -> f a = g a) -> filter f l = filter g l.
    Proof.
      intros f g l H. (* GOAL #105 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #105: 
Tactic call ran for 0.056 secs (0.016u,0.015s) (failure)
The command has indeed failed with message:
Solver error: (error argument type is not a subtype of the function's argument type:
argument:  op_1
has type:  (-> Tindex_0 Bool)
not subtype: Bool
in term : (op_3 (as op_1 Bool) op_2) ).
*)
(* RESULT #105: N/A. Not subtype. *)rewrite filter_map. apply map_ext_in. auto.
    Qed.

    Lemma ext_in_filter : forall (f g : A -> bool) (l : list A),
      filter f l = filter g l -> (forall a, In a l -> f a = g a).
    Proof.
      intros f g l H. (* GOAL #106 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #106: 
Discarding the following lemma (unsupported): (In a l : Prop)
[Lemma,SMTCoq plugin]
Tactic call ran for 0.009 secs (0.009u,0.s) (failure)
The command has indeed failed with message:
Anomaly "Uncaught exception Invalid_argument("index out of bounds")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #106: N/A. Out of bounds. Rewrite in hyp. *)
rewrite filter_map in H. apply ext_in_map. assumption.
    Qed.

    Lemma filter_ext_in_iff : forall (f g : A -> bool) (l : list A),
      filter f l = filter g l <-> (forall a, In a l -> f a = g a).
    Proof.
      split; [apply ext_in_filter | apply filter_ext_in].
    Qed.

    Lemma filter_ext : forall (f g : A -> bool),
      (forall a, f a = g a) -> forall l, filter f l = filter g l.
    Proof.
      intros f g H l. (* GOAL #107 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #107: 
Tactic call ran for 0.054 secs (0.006u,0.016s) (failure)
The command has indeed failed with message:
Solver error: (error argument type is not a subtype of the function's argument type:
argument:  op_1
has type:  (-> Tindex_0 Bool)
not subtype: Bool
in term : (op_3 (as op_1 Bool) op_2) ).
*)
(* RESULT #107: N/A. Not subtype. *)rewrite filter_map. apply map_ext. assumption.
    Qed.

    (** Remove by filtering *)

    Hypothesis eq_dec : forall x y : A, {x = y}+{x <> y}.

    Definition remove' (x : A) : list A -> list A :=
      filter (fun y => if eq_dec x y then false else true).

    Lemma remove_alt (x : A) (l : list A) : remove' x l = remove eq_dec x l.
    Proof with intuition.
      induction l...
      simpl. destruct eq_dec; f_equal...
    Qed.

    (** Counting occurrences by filtering *)

    Definition count_occ' (l : list A) (x : A) : nat :=
      length (filter (fun y => if eq_dec y x then true else false) l).

    Lemma count_occ_alt (l : list A) (x : A) :
      count_occ' l x = count_occ eq_dec l x.
    Proof with intuition.
      unfold count_occ'. induction l...
      simpl; destruct eq_dec; simpl...
    Qed.

  End Filtering.


  (******************************************************)
  (** ** Operations on lists of pairs or lists of lists *)
  (******************************************************)

  Section ListPairs.
    Variables (A : Type) (B : Type).

  (** [split] derives two lists from a list of pairs *)

    Fixpoint split (l:list (A*B)) : list A * list B :=
      match l with
      | [] => ([], [])
      | (x,y) :: tl => let (left,right) := split tl in (x::left, y::right)
      end.

    Lemma in_split_l : forall (l:list (A*B))(p:A*B),
      In p l -> In (fst p) (fst (split l)).
    Proof.
      intro l; induction l as [|a l IHl]; simpl; intros p H; auto.
      destruct p as [a0 b]; destruct a; destruct (split l); simpl in *.
      destruct H as [H|H].
      injection H; auto.
      right; apply (IHl (a0,b) H).
    Qed.

    Lemma in_split_r : forall (l:list (A*B))(p:A*B),
      In p l -> In (snd p) (snd (split l)).
    Proof.
      intro l; induction l as [|a l IHl]; simpl; intros p H; auto.
      destruct p as [a0 b]; destruct a; destruct (split l); simpl in *.
      destruct H as [H|H].
      injection H; auto.
      right; apply (IHl (a0,b) H).
    Qed.

    Lemma split_nth : forall (l:list (A*B))(n:nat)(d:A*B),
      nth n l d = (nth n (fst (split l)) (fst d), nth n (snd (split l)) (snd d)).
    Proof.
      intro l; induction l as [|a l IHl].
      intros n d; destruct n; destruct d; simpl; auto.
      intros n d; destruct n; destruct d; simpl; auto.
      destruct a; destruct (split l); simpl; auto.
      destruct a; destruct (split l); simpl in *; auto.
      apply IHl.
    Qed.

    Lemma split_length_l : forall (l:list (A*B)),
      length (fst (split l)) = length l.
    Proof.
      intro l; induction l as [|a l IHl]; simpl; auto.
      destruct a; destruct (split l); simpl; auto.
    Qed.

    Lemma split_length_r : forall (l:list (A*B)),
      length (snd (split l)) = length l.
    Proof.
      intro l; induction l as [|a l IHl]; simpl; auto.
      destruct a; destruct (split l); simpl; auto.
    Qed.

  (** [combine] is the opposite of [split].
      Lists given to [combine] are meant to be of same length.
      If not, [combine] stops on the shorter list *)

    Fixpoint combine (l : list A) (l' : list B) : list (A*B) :=
      match l,l' with
      | x::tl, y::tl' => (x,y)::(combine tl tl')
      | _, _ => nil
      end.

    Lemma split_combine : forall (l: list (A*B)),
      let (l1,l2) := split l in combine l1 l2 = l.
    Proof.
      intro l; induction l as [|a l IHl].
      simpl; auto.
      destruct a; simpl.
      destruct (split l); simpl in *.
      f_equal; auto.
    Qed.

    Lemma combine_split : forall (l:list A)(l':list B), length l = length l' ->
      split (combine l l') = (l,l').
    Proof.
      intro l; induction l as [|a l IHl]; intro l'; destruct l';
       simpl; trivial; try discriminate.
      now intros [= ->%IHl].
    Qed.

    Lemma in_combine_l : forall (l:list A)(l':list B)(x:A)(y:B),
      In (x,y) (combine l l') -> In x l.
    Proof.
      intro l; induction l as [|a l IHl].
      simpl; auto.
      intro l'; destruct l' as [|a0 l']; simpl; auto; intros x y H.
      contradiction.
      destruct H as [H|H].
      injection H; auto.
      right; apply IHl with l' y; auto.
    Qed.

    Lemma in_combine_r : forall (l:list A)(l':list B)(x:A)(y:B),
      In (x,y) (combine l l') -> In y l'.
    Proof.
      intro l; induction l as [|? ? IHl].
      simpl; intros; contradiction.
      intro l'; destruct l'; simpl; auto; intros x y H.
      destruct H as [H|H].
      injection H; auto.
      right; apply IHl with x; auto.
    Qed.

    Lemma combine_length : forall (l:list A)(l':list B),
      length (combine l l') = min (length l) (length l').
    Proof.
      intro l; induction l.
      simpl; auto.
      intro l'; destruct l'; simpl; auto.
    Qed.

    Lemma combine_nth : forall (l:list A)(l':list B)(n:nat)(x:A)(y:B),
      length l = length l' ->
      nth n (combine l l') (x,y) = (nth n l x, nth n l' y).
    Proof.
      intro l; induction l; intro l'; destruct l'; intros n x y; try discriminate.
      destruct n; simpl; auto.
      destruct n; simpl in *; auto.
    Qed.

  (** [list_prod] has the same signature as [combine], but unlike
     [combine], it adds every possible pairs, not only those at the
     same position. *)

    Fixpoint list_prod (l:list A) (l':list B) :
      list (A * B) :=
      match l with
      | nil => nil
      | cons x t => (map (fun y:B => (x, y)) l')++(list_prod t l')
      end.

    Lemma in_prod_aux :
      forall (x:A) (y:B) (l:list B),
	In y l -> In (x, y) (map (fun y0:B => (x, y0)) l).
    Proof.
(* GOAL #108 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #108: *)
(* RESULT #108: N/A. Deeply nested.*)
      intros x y l; induction l;
	[ simpl; auto
	  | simpl; destruct 1 as [H1| ];
	    [ left; rewrite H1; trivial | right; auto ] ].
    Qed.

    Lemma in_prod :
      forall (l:list A) (l':list B) (x:A) (y:B),
        In x l -> In y l' -> In (x, y) (list_prod l l').
    Proof.
(* GOAL #109 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #109: *)
(* RESULT #109: N/A. Deeply nested. *)
      intro l; induction l;
      [ simpl; tauto
        | simpl; intros l' x y H H0; apply in_or_app; destruct H as [H|H];
          [ left; rewrite H; apply in_prod_aux; assumption | right; auto ] ].
    Qed.

    Lemma in_prod_iff :
      forall (l:list A)(l':list B)(x:A)(y:B),
        In (x,y) (list_prod l l') <-> In x l /\ In y l'.
    Proof.
      intros l l' x y; split; [ | intros H; apply in_prod; intuition ].
      induction l as [|a l IHl]; simpl; intros H.
      intuition.
      destruct (in_app_or _ _ _ H) as [H0|H0]; clear H.
      destruct (in_map_iff (fun y : B => (a, y)) l' (x,y)) as (H1,_).
      destruct (H1 H0) as (z,(H2,H3)); clear H0 H1.
      injection H2 as [= -> ->]; intuition.
      intuition.
    Qed.

    Lemma prod_length : forall (l:list A)(l':list B),
      length (list_prod l l') = (length l) * (length l').
    Proof.
      intro l; induction l; simpl; auto.
      intros. (* GOAL #110 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #110: 
Tactic call ran for 0.056 secs (0.019u,0.008s) (failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName3 Tindex_2)) (= (op_2 (op_1 op_0 SMTCoqRelName3)) (op_5 (op_3 op_0) (op_4 SMTCoqRelName3))) ) ).
*)
(* RESULT #110: N/A. Quantified. *)
      rewrite app_length. (* GOAL #111 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #111: 
Tactic call ran for 0.048 secs (0.013u,0.008s) (failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName4 Tindex_2)) (= (op_2 (op_1 op_0 SMTCoqRelName4)) (op_5 (op_3 op_0) (op_4 SMTCoqRelName4))) ) ).
*)
(* RESULT #111: N/A. Quantified. *)
      rewrite map_length.
      auto.
    Qed.

  End ListPairs.




(*****************************************)
(** * Miscellaneous operations on lists  *)
(*****************************************)



(******************************)
(** ** Length order of lists  *)
(******************************)

Section length_order.
  Variable A : Type.

  Definition lel (l m:list A) := length l <= length m.

  Variables a b : A.
  Variables l m n : list A.

  Lemma lel_refl : lel l l.
  Proof.
    unfold lel; auto with arith.
  Qed.

  Lemma lel_trans : lel l m -> lel m n -> lel l n.
  Proof.
    unfold lel; intros.
    now_show (length l <= length n).
    apply le_trans with (length m); auto with arith.
  Qed.

  Lemma lel_cons_cons : lel l m -> lel (a :: l) (b :: m).
  Proof.
    unfold lel; simpl; auto with arith.
  Qed.

  Lemma lel_cons : lel l m -> lel l (b :: m).
  Proof.
    unfold lel; simpl; auto with arith.
  Qed.

  Lemma lel_tail : lel (a :: l) (b :: m) -> lel l m.
  Proof.
    unfold lel; simpl; auto with arith.
  Qed.

  Lemma lel_nil : forall l':list A, lel l' nil -> nil = l'.
  Proof.
    intro l'; elim l'; auto with arith.
    intros a' y H H0.
    now_show (nil = a' :: y).
    absurd (S (length y) <= 0); auto with arith.
  Qed.
End length_order.

#[global]
Hint Resolve lel_refl lel_cons_cons lel_cons lel_nil lel_nil nil_cons:
  datatypes.


(******************************)
(** ** Set inclusion on list  *)
(******************************)

Section SetIncl.

  Variable A : Type.

  Definition incl (l m:list A) := forall a:A, In a l -> In a m.
  #[local]
  Hint Unfold incl : core.

  Lemma incl_nil_l : forall l, incl nil l.
  Proof.
    intros l a Hin; inversion Hin.
  Qed.

  Lemma incl_l_nil : forall l, incl l nil -> l = nil.
  Proof.
    intro l; destruct l as [|a l]; intros Hincl.
    - reflexivity.
    - exfalso; apply Hincl with a; simpl; auto.
  Qed.

  Lemma incl_refl : forall l:list A, incl l l.
  Proof.
    auto.
  Qed.
  #[local]
  Hint Resolve incl_refl : core.

  Lemma incl_tl : forall (a:A) (l m:list A), incl l m -> incl l (a :: m).
  Proof.
    auto with datatypes.
  Qed.
  #[local]
  Hint Immediate incl_tl : core.

  Lemma incl_tran : forall l m n:list A, incl l m -> incl m n -> incl l n.
  Proof.
    auto.
  Qed.

  Lemma incl_appl : forall l m n:list A, incl l n -> incl l (n ++ m).
  Proof.
    auto with datatypes.
  Qed.
  #[local]
  Hint Immediate incl_appl : core.

  Lemma incl_appr : forall l m n:list A, incl l n -> incl l (m ++ n).
  Proof.
    auto with datatypes.
  Qed.
  #[local]
  Hint Immediate incl_appr : core.

  Lemma incl_cons :
    forall (a:A) (l m:list A), In a m -> incl l m -> incl (a :: l) m.
  Proof.
    unfold incl; simpl; intros a l m H H0 a0 H1.
    now_show (In a0 m).
    elim H1.
    now_show (a = a0 -> In a0 m).
    elim H1; auto; intro H2.
    now_show (a = a0 -> In a0 m).
    elim H2; auto. (* solves subgoal *)
    now_show (In a0 l -> In a0 m).
    auto.
  Qed.
  #[local]
  Hint Resolve incl_cons : core.

  Lemma incl_cons_inv : forall (a:A) (l m:list A),
    incl (a :: l) m -> In a m /\ incl l m.
  Proof.
    intros a l m Hi.
    split; [ | intros ? ? ]; apply Hi; simpl; auto.
  Qed.

  Lemma incl_app : forall l m n:list A, incl l n -> incl m n -> incl (l ++ m) n.
  Proof.
    unfold incl; simpl; intros l m n H H0 a H1.
    now_show (In a n).
    elim (in_app_or _ _ _ H1); auto.
  Qed.
  #[local]
  Hint Resolve incl_app : core.

  Lemma incl_app_app : forall l1 l2 m1 m2:list A,
    incl l1 m1 -> incl l2 m2 -> incl (l1 ++ l2) (m1 ++ m2).
  Proof.
    intros.
    apply incl_app; [ apply incl_appl | apply incl_appr]; assumption.
  Qed.

  Lemma incl_app_inv : forall l1 l2 m : list A,
    incl (l1 ++ l2) m -> incl l1 m /\ incl l2 m.
  Proof.
    intro l1; induction l1 as [|a l1 IHl1]; intros l2 m Hin; split; auto.
    - apply incl_nil_l.
    - intros b Hb; inversion_clear Hb; subst; apply Hin.
      + now constructor.
      + simpl; apply in_cons.
        apply incl_appl with l1; [ apply incl_refl | assumption ].
    - apply IHl1.
      now apply incl_cons_inv in Hin.
  Qed.

  Lemma incl_filter f l : incl (filter f l) l.
  Proof. intros x Hin; now apply filter_In in Hin. Qed.

  Lemma remove_incl (eq_dec : forall x y : A, {x = y} + {x <> y}) : forall l1 l2 x,
    incl l1 l2 -> incl (remove eq_dec x l1) (remove eq_dec x l2).
  Proof.
    intros l1 l2 x Hincl y Hin.
    apply in_remove in Hin; destruct Hin as [Hin Hneq].
    apply in_in_remove; intuition.
  Qed.

End SetIncl.

Lemma incl_map A B (f : A -> B) l1 l2 : incl l1 l2 -> incl (map f l1) (map f l2).
Proof.
  intros Hincl x Hinx.
  destruct (proj1 (in_map_iff _ _ _) Hinx) as [y [<- Hiny]].
  apply in_map; intuition.
Qed.

#[global]
Hint Resolve incl_refl incl_tl incl_tran incl_appl incl_appr incl_cons
  incl_app incl_map: datatypes.


(**************************************)
(** * Cutting a list at some position *)
(**************************************)

Section Cutting.

  Variable A : Type.

  Fixpoint firstn (n:nat)(l:list A) : list A :=
    match n with
      | 0 => nil
      | S n => match l with
		 | nil => nil
		 | a::l => a::(firstn n l)
	       end
    end.

  Lemma firstn_nil n: firstn n [] = [].
  Proof. induction n; now simpl. Qed.

  Lemma firstn_cons n a l: firstn (S n) (a::l) = a :: (firstn n l).
  Proof. now simpl. Qed.

  Lemma firstn_all l: firstn (length l) l = l.
  Proof. induction l as [| ? ? H]; simpl. reflexivity. (* verit. admit. admit. *)
        (* GOAL #112 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #112: 
The command has not failed!
Tactic call ran for 0.085 secs (0.013u,0.007s) (success)
*)
(* RESULT #112: Smt Success. Local lemma. *) rewrite H. easy.  Qed.

  Lemma firstn_all2 n: forall (l:list A), (length l) <= n -> firstn n l = l.
  Proof. induction n as [|k iHk].
    - intro l. inversion 1 as [H1|?].
(* GOAL #113 *) (* Fail Timeout 20 (time abduce 3). *)
(*  Search (firstn (length _) _ = _).
  assert ((firstn ((length (A:=A)) l) l) = l). { apply firstn_all. } smt. *)
(* OUTPUT #113: 
cvc5 returned SAT.
The solver cannot prove the goal, but one of the following hypotheses (printed in Prop, but the corresponding Boolean versions also apply) would make it provable:
(firstn 0 l) = l
(firstn ((length (A:=A)) l) l) = l
(not (not (firstn 0 l) = l) && ((length (A:=A)) l) = 0)*)
(* RESULT #113: Success. *)
      rewrite (length_zero_iff_nil l) in H1. subst. now simpl.
    - intro l; destruct l as [|x xs]; simpl.
      * now reflexivity.
      * simpl. intro H. apply Peano.le_S_n in H. f_equal. apply iHk, H.
  Qed.

  Lemma firstn_O l: firstn 0 l = [].
  Proof. now simpl. Qed.

  Lemma firstn_le_length n: forall l:list A, length (firstn n l) <= n.
  Proof.
    induction n as [|k iHk]; simpl; [auto | intro l; destruct l as [|x xs]; simpl].
    - auto with arith.
    - apply Peano.le_n_S, iHk.
  Qed.

  Lemma firstn_length_le: forall l:list A, forall n:nat,
    n <= length l -> length (firstn n l) = n.
  Proof. intro l; induction l as [|x xs Hrec].
    - simpl. intros n H. apply le_n_0_eq in H. 
(* GOAL #114 *)
(* assert (length (firstn 0 []) = 0) by admit.
Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #114: 
The command has not failed!
Tactic call ran for 0.043 secs (0.013u,0.012s) (success) *)
(* RESULT #114: Smt success. Poked holes. *)rewrite <- H. now simpl.
    - intro n; destruct n as [|n].
      * now simpl.
      * simpl. intro H. apply le_S_n in H. 
        (* GOAL #115 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #115: 
Discarding the following lemma (unsupported): (n <= length xs : Prop)
[Lemma,SMTCoq plugin]
Tactic call ran for 0.081 secs (0.031u,0.008s) (failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName1 Tindex_0)) (= SMTCoqRelName1 (op_2 (op_1 SMTCoqRelName1 op_0))) ) ).
*)
(* RESULT #115: N/A. Quantified. Local lemma. *)now rewrite (Hrec n H).
  Qed.

  Lemma firstn_app n:
    forall l1 l2,
    firstn n (l1 ++ l2) = (firstn n l1) ++ (firstn (n - length l1) l2).
  Proof. induction n as [|k iHk]; intros l1 l2.
    - now simpl.
    - destruct l1 as [|x xs].
      * unfold firstn at 2, length. 
(* GOAL #116 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #116: 
Tactic call ran for 0.062 secs (0.006u,0.019s) (failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName2 Tindex_0) (SMTCoqRelName3 Tindex_0)) (= (op_2 op_0 (op_1 SMTCoqRelName3 SMTCoqRelName2)) (op_1 (op_2 op_0 SMTCoqRelName3) (op_2 (op_4 op_0 (op_3 SMTCoqRelName3)) SMTCoqRelName2))) ) ).
*)
(* RESULT #116: N/A. Quantified. *)rewrite 2!app_nil_l.
(* GOAL #117 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #117: 
Tactic call ran for 0.075 secs (0.019u,0.011s) (failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName4 Tindex_0) (SMTCoqRelName5 Tindex_0)) (= (op_2 op_0 (op_1 SMTCoqRelName5 SMTCoqRelName4)) (op_1 (op_2 op_0 SMTCoqRelName5) (op_2 (op_4 op_0 (op_3 SMTCoqRelName5)) SMTCoqRelName4))) ) ).
*)
(* RESULT #117: N/A. Quantified. *)
rewrite <- minus_n_O. easy.
      * (* GOAL #118 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #118: 
Tactic call ran for 0.074 secs (0.01u,0.011s) (failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName6 Tindex_0) (SMTCoqRelName7 Tindex_0)) (= (op_2 op_0 (op_1 SMTCoqRelName7 SMTCoqRelName6)) (op_1 (op_2 op_0 SMTCoqRelName7) (op_2 (op_4 op_0 (op_3 SMTCoqRelName7)) SMTCoqRelName6))) ) ).
*)
(* RESULT #118: N/A. Quantified. *)rewrite <- app_comm_cons. simpl. f_equal. apply iHk.
  Qed.

  Lemma firstn_app_2 n:
    forall l1 l2,
    firstn ((length l1) + n) (l1 ++ l2) = l1 ++ firstn n l2.
  Proof. induction n as [| k iHk];intros l1 l2.
    - unfold firstn at 2. 
(* GOAL #119 *)
(* assert (l1 ++ [] = l1) by admit. (* app_nil_r *)
assert ((firstn (length l1) (l1 ++ l2) = firstn (length l1) l1 ++ firstn (length l1 - length l1) l2)) by admit. (* firstn_app *)
assert (length l1 - length l1 = 0) by admit. (* minus_diag_reverse *)
assert (firstn 0 l2 = []) by admit. (* unfold firstn at 2 *)
assert (firstn (length l1) l1 = l1) by admit. (* firstn_all *)
Fail Timeout 20 (time abduce 1).
assert ((Init.Nat.add ((length (A:=A)) l1) 0) = ((length (A:=A)) l1)).
{ Search (_ + 0 = _). apply Nat.add_0_r. } smt. *)
(* OUTPUT #119:
Tactic call ran for 13.578 secs (0.025u,0.026s) (failure)
The command has indeed failed with message:
cvc5 returned SAT.
The solver cannot prove the goal, but one of the following hypotheses (printed in Prop, but the corresponding Boolean versions also apply) would make it provable:
(Init.Nat.add ((length (A:=A)) l1) 0) = ((length (A:=A)) l1) *)
(* RESULT #119: Success. Poked holes. *)rewrite <- plus_n_O.
(* GOAL #120 *) 
(* assert ((firstn (length l1) (l1 ++ l2) = firstn (length l1) l1 ++ firstn (length l1 - length l1) l2)) by admit. (* firstn_app *)
assert (length l1 - length l1 = 0) by admit. (* minus_diag_reverse *)
assert (firstn 0 l2 = []) by admit. (* unfold firstn at 2 *)
assert (firstn (length l1) l1 = l1) by admit. (* firstn_all *)
Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #120: 
The command has not failed!
Tactic call ran for 0.046 secs (0.018u,0.011s) (success)
*)
(* RESULT #120: Smt success. Poked holes. *)
      rewrite app_nil_r. 
(* GOAL #121 *) 
(* assert (length l1 - length l1 = 0) by admit. (* minus_diag_reverse *)
assert (firstn 0 l2 = []) by admit. (* unfold firstn at 2 *)
assert (firstn (length l1) l1 = l1) by admit. (* firstn_all *)
Fail Timeout 20 (time abduce 4). *)
(* OUTPUT #121: 
Tactic call ran for 5.765 secs (0.011u,0.023s) (failure)
The command has indeed failed with message:
cvc5 returned SAT.
The solver cannot prove the goal, but one of the following hypotheses (printed in Prop, but the corresponding Boolean versions also apply) would make it provable:
((app (A:=A)) l1 l2) = l1
(firstn ((length (A:=A)) l1) ((app (A:=A)) l1 l2)) = l1
(firstn ((length (A:=A)) l1) l1) = ((app (A:=A)) l1 l2)
((app (A:=A)) (firstn ((length (A:=A)) l1) l1) l2) = l1
*)
(* RESULT #121: Failure. Poked holes. *)
      rewrite firstn_app.
(* GOAL #122 *)
(* assert (firstn 0 l2 = []) by admit. (* unfold firstn at 2 *)
assert (firstn (length l1) l1 = l1) by admit. (* firstn_all *)
Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #122: 
The command has indeed failed with message:
Timeout!
*)
(* RESULT #122: Failure. Poked holes. *) rewrite <- minus_diag_reverse.
      unfold firstn at 2.
(* GOAL #123 *) 
(* assert (firstn (length l1) l1 = l1) by admit. (* firstn_all *)
Fail Timeout 20 (time abduce 1).
assert (((app (A:=A)) l1 []) = l1).
{ Search (_ ++ [] = _). apply app_nil_r. } smt.
 *)
(* OUTPUT #123: 
Tactic call ran for 0.108 secs (0.003u,0.021s) (failure)
The command has indeed failed with message:
cvc5 returned SAT.
The solver cannot prove the goal, but one of the following hypotheses (printed in Prop, but the corresponding Boolean versions also apply) would make it provable:
((app (A:=A)) l1 []) = l1
*)
(* RESULT #123: Success. Poked holes. *)
rewrite app_nil_r. apply firstn_all.
    - destruct l2 as [|x xs].
      * simpl. (* GOAL #124 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #124: 
Tactic call ran for 0.083 secs (0.015u,0.016s) (failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName8 Tindex_0) (SMTCoqRelName9 Tindex_0)) (= (op_4 (op_2 (op_0 SMTCoqRelName9) op_1) (op_3 SMTCoqRelName9 SMTCoqRelName8)) (op_3 SMTCoqRelName9 (op_4 op_1 SMTCoqRelName8))) ) ).
*)
(* RESULT #124: N/A. Quantified. *)rewrite app_nil_r. apply firstn_all2. auto with arith.
      * (* GOAL #125 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #125: 
Tactic call ran for 0.073 secs (0.016u,0.012s) (failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName10 Tindex_0) (SMTCoqRelName11 Tindex_0)) (= (op_4 (op_2 (op_0 SMTCoqRelName11) op_1) (op_3 SMTCoqRelName11 SMTCoqRelName10)) (op_3 SMTCoqRelName11 (op_4 op_1 SMTCoqRelName10))) ) ).
*)
(* RESULT #125: N/A. Quantified. *)rewrite firstn_app. assert (H0 : (length l1 + S k - length l1) = S k).
        auto with arith.
        (* GOAL #126 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #126: 
Tactic call ran for 0.086 secs (0.022u,0.015s) (failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName12 Tindex_0) (SMTCoqRelName13 Tindex_0)) (= (op_4 (op_2 (op_0 SMTCoqRelName13) op_1) (op_3 SMTCoqRelName13 SMTCoqRelName12)) (op_3 SMTCoqRelName13 (op_4 op_1 SMTCoqRelName12))) ) ).
*)
(* RESULT #126: N/A. Quantified. Local lemma. *)rewrite H0, firstn_all2; [reflexivity | auto with arith].
  Qed.

  Lemma firstn_firstn:
    forall l:list A,
    forall i j : nat,
    firstn i (firstn j l) = firstn (min i j) l.
  Proof. intro l; induction l as [|x xs Hl].
    - intros. simpl. (* GOAL #127 *)
(* assert (firstn i [] = []) by admit.
assert (firstn (Init.Nat.min i j) [] = []) by admit.
Fail Timeout 20 (time abduce 2).
assert ((firstn j []) = []).
{ Search (firstn _ [] = []). apply firstn_nil. } smt. *)
(* OUTPUT #127: 
Tactic call ran for 0.159 secs (0.029u,0.024s) (failure)
The command has indeed failed with message:
cvc5 returned SAT.
The solver cannot prove the goal, but one of the following hypotheses (printed in Prop, but the corresponding Boolean versions also apply) would make it provable:
i = j
(firstn j []) = []*)
(* RESULT #127: Success. Poked holes. *) 
rewrite firstn_nil.
(* GOAL #127.2 *)
(* assert (firstn (Init.Nat.min i j) [] = []) by admit.
 Fail Timeout 20 (time abduce 1).
assert ((firstn i []) = []). 
{ Search (firstn _ [] = []). apply firstn_nil. } smt. *)
(* OUTPUT #127.2:
Tactic call ran for 0.159 secs (0.008u,0.03s) (failure)
The command has indeed failed with message:
cvc5 returned SAT.
The solver cannot prove the goal, but one of the following hypotheses (printed in Prop, but the corresponding Boolean versions also apply) would make it provable:
(firstn i []) = [] *)
(* RESULT #127.2: Success. Poked holes. *)
rewrite firstn_nil.
(* GOAL #127.3 *)
(* Fail Timeout 20 (time abduce 1).
assert ((firstn (Init.Nat.min i j) []) = []).
{ Search (firstn _ [] = []). apply firstn_nil. } smt. *)
(* OUTPUT #127.3:
Tactic call ran for 0.238 secs (0.002u,0.026s) (failure)
The command has indeed failed with message:
cvc5 returned SAT.
The solver cannot prove the goal, but one of the following hypotheses (printed in Prop, but the corresponding Boolean versions also apply) would make it provable:
(firstn (Init.Nat.min i j) []) = [] *)
(* RESULT #127.3: Success. *)
now rewrite firstn_nil.
    - intro i; destruct i.
      * intro. now simpl.
      * intro j; destruct j.
        + now simpl.
        + simpl. f_equal. apply Hl.
  Qed.

  Fixpoint skipn (n:nat)(l:list A) : list A :=
    match n with
      | 0 => l
      | S n => match l with
		 | nil => nil
		 | a::l => skipn n l
	       end
    end.

  Lemma firstn_skipn_comm : forall m n l,
  firstn m (skipn n l) = skipn n (firstn (n + m) l).
  Proof. now intros m n; induction n; intros []; simpl; destruct m. Qed.

  Lemma skipn_firstn_comm : forall m n l,
  skipn m (firstn n l) = firstn (n - m) (skipn m l).
  Proof. intro m; induction m; intros [] []; simpl; try easy. 
(* GOAL #128 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #128: 
Tactic call ran for 0.05 secs (0.008u,0.007s) (failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName14 Tindex_0) (SMTCoqRelName15 Tindex_1)) (= (op_2 op_0 (op_1 SMTCoqRelName15 SMTCoqRelName14)) (op_1 (op_3 SMTCoqRelName15 op_0) (op_2 op_0 SMTCoqRelName14))) ) ).
*)
(* RESULT #128: N/A. Quantified. *)rewrite ?firstn_nil. easy. Qed.

  Lemma skipn_O : forall l, skipn 0 l = l.
  Proof. reflexivity. Qed.

  Lemma skipn_nil : forall n, skipn n ([] : list A) = [].
  Proof. now intros []. Qed.

  Lemma skipn_cons n a l: skipn (S n) (a::l) = skipn n l.
  Proof. reflexivity. Qed.

  Lemma skipn_all : forall l, skipn (length l) l = nil.
  Proof. now intro l; induction l. Qed.

#[deprecated(since="8.12",note="Use skipn_all instead.")] Notation skipn_none := skipn_all.

  Lemma skipn_all2 n: forall l, length l <= n -> skipn n l = [].
  Proof.
    intros l L%Nat.sub_0_le. 
(* GOAL #129 *) 
(* assert ((skipn n (firstn (length l) l) = firstn (length l - n) (skipn n l))) by admit.
assert (firstn 0 (skipn n l) = []) by admit.
Fail Timeout 20 (time abduce 2). *)
(* OUTPUT #129:
Tactic call ran for 10.065 secs (0.027u,0.023s) (failure)
The command has indeed failed with message:
cvc5 returned SAT.
The solver cannot prove the goal, but one of the following hypotheses (printed in Prop, but the corresponding Boolean versions also apply) would make it provable:
(skipn n l) = []
(firstn 0 (skipn n l)) = (skipn n l) *)
(* RESULT #129: Failure. Poked holes. *)
    rewrite <-(firstn_all l) at 1.
(* GOAL #130 *) 
(* assert (firstn 0 (skipn n l) = []) by admit.
Fail Timeout 20 (time abduce 2). *)
(* OUTPUT #130: 
Tactic call ran for 5.158 secs (0.015u,0.033s) (failure)
The command has indeed failed with message:
cvc5 returned SAT.
The solver cannot prove the goal, but one of the following hypotheses (printed in Prop, but the corresponding Boolean versions also apply) would make it provable:
(skipn n (firstn ((length (A:=A)) l) l)) = []
*)
(* RESULT #130: Failure. Poked holes. asserts goal. *)
    rewrite skipn_firstn_comm.
(* GOAL #131 *) (* Fail Timeout 20 (time abduce 1). *) 
(* OUTPUT #131: 
The command has indeed failed with message:
Timeout!
*)
(* RESULT #131: Failure. Timeout. Local lemma. *)
   now rewrite L.
  Qed.

  Lemma firstn_skipn : forall n l, firstn n l ++ skipn n l = l.
  Proof.
    intro n; induction n.
    simpl; auto.
    intro l; destruct l; simpl; auto.
    f_equal; auto.
  Qed.

  Lemma firstn_length : forall n l, length (firstn n l) = min n (length l).
  Proof.
    intro n; induction n; intro l; destruct l; simpl; auto.
  Qed.

  Lemma skipn_length n :
    forall l, length (skipn n l) = length l - n.
  Proof.
    induction n.
    - intros l; simpl. (* GOAL #132 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #132: 
Tactic call ran for 0.655 secs (0.004u,0.023s) (failure)
The command has indeed failed with message:
cvc5 returned SAT.
The solver cannot prove the goal, but one of the following hypotheses (printed in Prop, but the corresponding Boolean versions also apply) would make it provable:
(Init.Nat.sub ((length (A:=A)) l) 0) = ((length (A:=A)) l)

*)
(* assert ((Init.Nat.sub ((length (A:=A)) l) 0) = ((length (A:=A)) l)). {
Search (_ - 0 = _). apply Nat.sub_0_r. } smt. *)
(* RESULT #132: Success. smt fails on Nat goal. *) 
rewrite Nat.sub_0_r; reflexivity.
    - intro l; destruct l; simpl; auto.
  Qed.

  Lemma skipn_app n : forall l1 l2,
    skipn n (l1 ++ l2) = (skipn n l1) ++ (skipn (n - length l1) l2).
  Proof. induction n; auto; intros [|]; simpl; auto. Qed.

  Lemma firstn_skipn_rev: forall x l,
      firstn x l = rev (skipn (length l - x) (rev l)).
  Proof.
    intros x l. rewrite <-(firstn_skipn x l) at 3.
(* GOAL #133 *) 
(* assert ((skipn (length l - x) (rev (skipn x l) ++ rev (firstn x l))) = 
  (skipn (length l - x) (rev (skipn x l)) ++
  skipn (length l - x - length (rev (skipn x l))) (rev (firstn x l)))) 
by admit. (* skipn_app *)
assert (rev (skipn (length l - x) (rev (skipn x l)) ++
  skipn (length l - x - length (rev (skipn x l))) (rev (firstn x l))) = 
  rev (skipn (length l - x - length (rev (skipn x l))) (rev (firstn x l))) ++
  rev (skipn (length l - x) (rev (skipn x l)))) by admit. (* rev_app_distr *)
assert ((length (rev (skipn x l))) = length (skipn x l)) by admit. (* rev_length *)
assert (length (skipn x l) = (length l - x)) by admit. (* skipn_length *)
assert ((length l - x - (length l - x)) = 0) by admit. (* Nat.sub_diag. *)
assert (skipn 0 (rev (firstn x l)) = rev (firstn x l)) by admit. (* simpl *)
assert (rev (rev (firstn x l)) = firstn x l) by admit. (* rev_involutive *)
assert (firstn x l = firstn x l ++ []) by admit. (* <- app_nil_r *)
assert (rev (skipn (length l - x) (rev (skipn x l))) = []) by admit. (* length_zero_iff_nil *)
Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #133: 
The command has indeed failed with message:
Timeout!
*)
(* RESULT #133: Failure. Poked holes. *)
    rewrite rev_app_distr.
(* GOAL #134 *) 
(* assert (rev (skipn (length l - x) (rev (skipn x l)) ++
  skipn (length l - x - length (rev (skipn x l))) (rev (firstn x l))) = 
  rev (skipn (length l - x - length (rev (skipn x l))) (rev (firstn x l))) ++
  rev (skipn (length l - x) (rev (skipn x l)))) by admit. (* rev_app_distr *)
assert ((length (rev (skipn x l))) = length (skipn x l)) by admit. (* rev_length *)
assert (length (skipn x l) = (length l - x)) by admit. (* skipn_length *)
assert ((length l - x - (length l - x)) = 0) by admit. (* Nat.sub_diag. *)
assert (skipn 0 (rev (firstn x l)) = rev (firstn x l)) by admit. (* simpl *)
assert (rev (rev (firstn x l)) = firstn x l) by admit. (* rev_involutive *)
assert (firstn x l = firstn x l ++ []) by admit. (* <- app_nil_r *)
assert (rev (skipn (length l - x) (rev (skipn x l))) = []) by admit. (* length_zero_iff_nil *)
Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #134: 
The command has indeed failed with message:
Timeout!
*)
(* RESULT #134: Failure. Poked holes. *) 
    rewrite skipn_app.
(* GOAL #135 *) 
(* assert ((length (rev (skipn x l))) = length (skipn x l)) by admit. (* rev_length *)
assert (length (skipn x l) = (length l - x)) by admit. (* skipn_length *)
assert ((length l - x - (length l - x)) = 0) by admit. (* Nat.sub_diag. *)
assert (skipn 0 (rev (firstn x l)) = rev (firstn x l)) by admit. (* simpl *)
assert (rev (rev (firstn x l)) = firstn x l) by admit. (* rev_involutive *)
assert (firstn x l = firstn x l ++ []) by admit. (* <- app_nil_r *)
assert (rev (skipn (length l - x) (rev (skipn x l))) = []) by admit. (* length_zero_iff_nil *)
Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #135: 
The command has indeed failed with message:
Timeout!
*)
(* RESULT #135: Failure. Poked holes. *) 
    rewrite rev_app_distr.
(* GOAL #136 *) 
(* assert (length (skipn x l) = (length l - x)) by admit. (* skipn_length *)
assert ((length l - x - (length l - x)) = 0) by admit. (* Nat.sub_diag. *)
assert (skipn 0 (rev (firstn x l)) = rev (firstn x l)) by admit. (* simpl *)
assert (rev (rev (firstn x l)) = firstn x l) by admit. (* rev_involutive *)
assert (firstn x l = firstn x l ++ []) by admit. (* <- app_nil_r *)
assert (rev (skipn (length l - x) (rev (skipn x l))) = []) by admit. (* length_zero_iff_nil *)
Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #136: 
The command has indeed failed with message:
Timeout!
*)
(* RESULT #136: Failure. Poked holes. *) 
    rewrite rev_length.
(* GOAL #137 *) 
(* assert ((length l - x - (length l - x)) = 0) by admit. (* Nat.sub_diag *)
assert (skipn 0 (rev (firstn x l)) = rev (firstn x l)) by admit. (* simpl *)
assert (rev (rev (firstn x l)) = firstn x l) by admit. (* rev_involutive *)
assert (firstn x l = firstn x l ++ []) by admit. (* <- app_nil_r *)
assert (rev (skipn (length l - x) (rev (skipn x l))) = []) by admit. (* length_zero_iff_nil *)
Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #137: 
The command has indeed failed with message:
Timeout!*)
(* RESULT #137: Failure. Poked holes. *)
    rewrite skipn_length.
(* GOAL #138 *)
(* assert (skipn 0 (rev (firstn x l)) = rev (firstn x l)) by admit. (* simpl *)
assert (rev (rev (firstn x l)) = firstn x l) by admit. (* rev_involutive *)
assert (firstn x l = firstn x l ++ []) by admit. (* <- app_nil_r *)
assert (rev (skipn (length l - x) (rev (skipn x l))) = []) by admit. (* length_zero_iff_nil *)
Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #138: 
The command has indeed failed with message:
Timeout!
*)
(* RESULT #138: Failure. Poked holes. *)
rewrite Nat.sub_diag. 
simpl.
(* GOAL #139 *) 
(* assert (firstn x l = firstn x l ++ []) by admit. (* <- app_nil_r *)
assert (rev (skipn (length l - x) (rev (skipn x l))) = []) by admit. (* length_zero_iff_nil *)
Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #139:
The command has indeed failed with message:
Timeout!*)
(* RESULT #139: Failure. Poked holes. *)
    rewrite rev_involutive.
(* GOAL #140 *) 
(* assert (rev (skipn (length l - x) (rev (skipn x l))) = []) by admit. (* length_zero_iff_nil *)
Fail Timeout 20 (time abduce 1).
assert (((app (A:=A)) (firstn x l) []) = (firstn x l)).
{  Search (_ ++ [] = _). apply app_nil_r. } smt. *)
(* OUTPUT #140: Tactic call ran for 6.736 secs (0.016u,0.021s) (failure)
The command has indeed failed with message:
cvc5 returned SAT.
The solver cannot prove the goal, but one of the following hypotheses (printed in Prop, but the corresponding Boolean versions also apply) would make it provable:
((app (A:=A)) (firstn x l) []) = (firstn x l) *)
(* RESULT #140: Success. Poked holes. *)
    rewrite <-app_nil_r at 1.
f_equal. symmetry. 
apply length_zero_iff_nil.
(* GOAL #141 *)
(* assert (length (skipn (length l - x) (rev (skipn x l))) = length (rev (skipn x l)) - (length l - x)) by admit. (* skipn_length *)
assert (length (rev (skipn x l)) = length (skipn x l)) by admit. (* rev_length *)
assert (length (skipn x l) = length l - x) by admit. (* skipn_length *)
assert (length l - x - (length l - x) = 0) by admit. (* Nat.sub_diag *)
Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #141: 
The command has indeed failed with message:
Timeout!
*)
(* RESULT #141: Failure. Poked holes. *)
    rewrite rev_length.
(* GOAL #142 *) 
(* assert (length (rev (skipn x l)) = length (skipn x l)) by admit. (* rev_length *)
assert (length (skipn x l) = length l - x) by admit. (* skipn_length *)
assert (length l - x - (length l - x) = 0) by admit. (* Nat.sub_diag *)
Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #142: 
The command has indeed failed with message:
Timeout!*)
(* RESULT #142: Failure. Poked holes. *)
    rewrite skipn_length.
(* GOAL #143 *) 
(* assert (length (skipn x l) = length l - x) by admit. (* skipn_length *)
assert (length l - x - (length l - x) = 0) by admit. (* Nat.sub_diag *)
Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #143: 
Tactic call ran for 5.229 secs (0.u,0.028s) (failure)
The command has indeed failed with message:
cvc5 returned SAT.
The solver cannot prove the goal, but one of the following hypotheses (printed in Prop, but the corresponding Boolean versions also apply) would make it provable:
((rev (A:=A)) (skipn x l)) = (skipn x l) *)
(* RESULT #143: Failure. Poked holes. *)
    rewrite rev_length.
(* GOAL #144 *)
(* assert (length l - x - (length l - x) = 0) by admit. (* Nat.sub_diag *)
Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #144: 
The command has indeed failed with message:
Timeout!*)
(* RESULT #144: Failure. Poked holes. *)
    rewrite skipn_length. 
apply Nat.sub_diag.
  Qed.

  Lemma firstn_rev: forall x l,
    firstn x (rev l) = rev (skipn (length l - x) l).
  Proof.
    intros x l.
(* GOAL #145 *) 
(* assert (rev (rev l) = l) by admit. (* rev_involutive *)
assert (length (rev l) = length l) by admit. (* rev_length *)
Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #145: 
The command has indeed failed with message:
Timeout!*)
(* RESULT #145: Failure. Poked holes. *)
    rewrite firstn_skipn_rev.
(* GOAL #146 *)
(* assert (length (rev l) = length l) by admit. (* rev_length *)
Fail Timeout 20 (time abduce 2).
assert (((rev (A:=A)) ((rev (A:=A)) l)) = l).
{ Search (rev (rev _) = _). apply rev_involutive. } smt. *)
(* OUTPUT #146: 
Tactic call ran for 0.433 secs (0.015u,0.019s) (failure)
The command has indeed failed with message:
cvc5 returned SAT.
The solver cannot prove the goal, but one of the following hypotheses (printed in Prop, but the corresponding Boolean versions also apply) would make it provable:
((rev (A:=A)) l) = l
((rev (A:=A)) ((rev (A:=A)) l)) = l *)
(* RESULT #146: Success. Poked holes. *)
    rewrite rev_involutive.
(* GOAL #147 *) (* Fail Timeout 20 (time abduce 2). *)
(* OUTPUT #147: 
Tactic call ran for 3.488 secs (0.006u,0.028s) (failure)
The command has indeed failed with message:
cvc5 returned SAT.
The solver cannot prove the goal, but one of the following hypotheses (printed in Prop, but the corresponding Boolean versions also apply) would make it provable:
((rev (A:=A)) l) = l
((length (A:=A)) ((rev (A:=A)) l)) = ((length (A:=A)) l)
*)
(* assert (((length (A:=A)) ((rev (A:=A)) l)) = ((length (A:=A)) l)). {
  Search (length (rev _) = length _). apply rev_length. } smt. *)
(* RESULT #147: Success. *)
    now rewrite rev_length.
  Qed.

  Lemma skipn_rev: forall x l,
      skipn x (rev l) = rev (firstn (length l - x) l).
  Proof.
    intros x l.
(* GOAL #148 *) 
(* assert (rev (rev (skipn (length l - (length l - x)) (rev l))) = skipn (length l - (length l - x)) (rev l)) by admit. (* rev_involutive *)
assert (length l = length (rev l)) by admit. (* <-rev_length *)
assert (skipn x (rev l) = skipn (length (rev l) - (length (rev l) - x)) (rev l)) by admit. (* destruct *)
Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #148: 
The command has indeed failed with message:
Timeout!
*)
(* RESULT #148: Failure. Poked holes. *)
    rewrite firstn_skipn_rev.
(* GOAL #149 *)
(* assert (length l = length (rev l)) by admit. (* <-rev_length *)
assert (skipn x (rev l) = skipn (length (rev l) - (length (rev l) - x)) (rev l)) by admit. (* destruct *)
Fail Timeout 20 (time abduce 2). *)
(* OUTPUT #149: 
Tactic call ran for 9.166 secs (0.023u,0.025s) (failure)
The command has indeed failed with message:
cvc5 returned SAT.
The solver cannot prove the goal, but one of the following hypotheses (printed in Prop, but the corresponding Boolean versions also apply) would make it provable:
(skipn x l) = l && ((rev (A:=A)) l) = l
((rev (A:=A)) (skipn x ((rev (A:=A)) l))) = (skipn x ((rev (A:=A)) l)) *)
(* RESULT #149: Failure. Poked holes. *)
    rewrite rev_involutive.
(* GOAL #150 *) 
(* assert (skipn x (rev l) = skipn (length (rev l) - (length (rev l) - x)) (rev l)) by admit. (* destruct *)
Fail Timeout 20 (time abduce 3).
assert (((length (A:=A)) ((rev (A:=A)) l)) = ((length (A:=A)) l)). 
{ Search (length (rev _) = length _). apply rev_length. } smt. *)
(* OUTPUT #150: 
Tactic call ran for 2.348 secs (0.011u,0.024s) (failure)
The command has indeed failed with message:
cvc5 returned SAT.
The solver cannot prove the goal, but one of the following hypotheses (printed in Prop, but the corresponding Boolean versions also apply) would make it provable:
((rev (A:=A)) l) = l
(Init.Nat.sub ((length (A:=A)) l) x) = x
((length (A:=A)) ((rev (A:=A)) l)) = ((length (A:=A)) l) *)
(* RESULT #150: Success. Poked holes. *) 
    rewrite <-rev_length.
    destruct (Nat.le_ge_cases (length (rev l)) x) as [L | L].
    - (* GOAL #151 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #151: 
Discarding the following lemma (unsupported): (length (rev l) <= x : Prop)
[Lemma,SMTCoq plugin]
Tactic call ran for 1.711 secs (0.002u,0.031s) (failure)
The command has indeed failed with message:
cvc5 returned SAT.
The solver cannot prove the goal, but one of the following hypotheses (printed in Prop, but the corresponding Boolean versions also apply) would make it provable:
(Init.Nat.sub ((length (A:=A)) ((rev (A:=A)) l)) x) = x
*)
(* RESULT #151: Failure. Unsound abduct. *) rewrite skipn_all2.
        + apply Nat.sub_0_le in L.
(* GOAL #152 *) 
(* assert (length (rev l) - 0 = length (rev l)) by admit. (* Nat.sub_0_r *)
assert (skipn (length (rev l)) (rev l) = []) by admit. (* skipn_all *)
Fail Timeout 20 (time abduce 1). 
assert ((Init.Nat.sub ((length (A:=A)) ((rev (A:=A)) l)) x) = 0). { Search (length (rev _) - _ = 0). apply L. } smt. *)
(* OUTPUT #152: 
Tactic call ran for 9.34 secs (0.023u,0.029s) (failure)
The command has indeed failed with message:
cvc5 returned SAT.
The solver cannot prove the goal, but one of the following hypotheses (printed in Prop, but the corresponding Boolean versions also apply) would make it provable:
(Init.Nat.sub ((length (A:=A)) ((rev (A:=A)) l)) x) = 0 *)
(* RESULT #152: Success. Poked holes. Local lemma. *)
        rewrite L.
(* GOAL #153 *)
(* assert (skipn (length (rev l)) (rev l) = []) by admit. (* skipn_all *)
Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #153: 
The command has indeed failed with message:
Timeout!*)
(* RESULT #153: Failure. Poked holes. *)
        rewrite Nat.sub_0_r.
(* GOAL #154 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #154: 
The command has indeed failed with message:
Timeout!
*)
(* RESULT #154: Failure. Timeout. *) 
        now rewrite skipn_all.
      + trivial.
    - replace (length (rev l) - (length (rev l) - x))
         with (length (rev l) + x - length (rev l)).
      (* GOAL #155 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #155: 
Discarding the following lemma (unsupported): (x <= length (rev l) : Prop)
[Lemma,SMTCoq plugin]
The command has indeed failed with message:
Timeout!
*)
(* RESULT #155: Failure. Can't poke holes. Drops nat lemma. *)
      rewrite minus_plus. reflexivity.
(* GOAL #156 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #156: 
Discarding the following lemma (unsupported): (x <= length (rev l) : Prop)
[Lemma,SMTCoq plugin]
The command has indeed failed with message:
Timeout!
*)
(* RESULT #156: Failure. Can't poke holes. Drops nat lemma. *)
      rewrite <- (Nat.sub_add _ _ L) at 2.
(* GOAL #157 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #157: 
Discarding the following lemma (unsupported): (x <= length (rev l) : Prop)
[Lemma,SMTCoq plugin]
The command has indeed failed with message:
Timeout!
*)
(* RESULT #157: Failure. Can't poke holes. Drops nat lemma. *)
      rewrite <-!(Nat.add_comm x).
(* GOAL #158 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #158: 
Discarding the following lemma (unsupported): (x <= length (rev l) : Prop)
[Lemma,SMTCoq plugin]
The command has indeed failed with message:
Timeout!
*)
(* RESULT #158: Failure. Can't poke holes. Drops nat lemma. *)
      now rewrite <-minus_plus_simpl_l_reverse.
  Qed.

   Lemma removelast_firstn : forall n l, n < length l ->
     removelast (firstn (S n) l) = firstn n l.
   Proof.
     intro n; induction n as [|n IHn]; intro l; destruct l as [|a l].
     simpl; auto.
     simpl; auto.
     simpl; auto.
     intros H.
     simpl in H.
     change (firstn (S (S n)) (a::l)) with ((a::nil)++firstn (S n) l).
     change (firstn (S n) (a::l)) with (a::firstn n l).
(* GOAL #159 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #159: 
Discarding the following lemma (unsupported): (S n < S (length l) : Prop)
[Lemma,SMTCoq plugin]
Tactic call ran for 0.116 secs (0.041u,0.04s) (failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName17 Tindex_0)) (= (op_3 (op_2 (op_1 op_0) SMTCoqRelName17)) (op_2 op_0 SMTCoqRelName17)) ) ).
*)
(* RESULT #159: N/A. Quantified. *)
     rewrite removelast_app.
(* GOAL #160 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #160: 
Discarding the following lemma (unsupported): (S n < S (length l) : Prop)
[Lemma,SMTCoq plugin]
Tactic call ran for 0.089 secs (0.029u,0.008s) (failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName19 Tindex_0)) (= (op_3 (op_2 (op_1 op_0) SMTCoqRelName19)) (op_2 op_0 SMTCoqRelName19)) ) ).
*)
(* RESULT #160: N/A. Quantified. Local lemma. *)
     rewrite IHn; auto with arith.
     clear IHn; destruct l; simpl in *; try discriminate.
     inversion_clear H as [|? H1].
     inversion_clear H1.
   Qed.

   Lemma removelast_firstn_len : forall l,
     removelast l = firstn (Nat.pred (length l)) l.
   Proof.
     intro l; induction l as [|a l IHl]; [ reflexivity | simpl ].
     destruct l. 
     easy.
(* GOAL #161 *) 
(* assert (a :: firstn (Nat.pred (length (a0 :: l))) (a0 :: l) =
firstn (length (a0 :: l)) (a :: a0 :: l)) by admit.
Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #161: 
The command has not failed!
Tactic call ran for 0.06 secs (0.027u,0.014s) (success) *)
(* RESULT #161: Smt success. Poked holes. Local lemma. *)
     rewrite IHl. reflexivity.
   Qed.

   Lemma firstn_removelast : forall n l, n < length l ->
     firstn n (removelast l) = firstn n l.
   Proof.
     intro n; induction n; intro l; destruct l as [|a l].
     simpl; auto.
     simpl; auto.
     simpl; auto.
     intros H.
     simpl in H.
     change (removelast (a :: l)) with (removelast ((a::nil)++l)).
(* GOAL #162 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #162: 
Discarding the following lemma (unsupported): (S n < S (length l) : Prop)
[Lemma,SMTCoq plugin]
Tactic call ran for 0.09 secs (0.032u,0.012s) (failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName21 Tindex_0)) (= (op_2 op_0 (op_1 SMTCoqRelName21)) (op_2 op_0 SMTCoqRelName21)) ) ).
*)
(* RESULT #162: N/A. Quantified. *)
     rewrite removelast_app.
     simpl; f_equal; auto with arith.
     intro H0. 
(* GOAL #163 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #163: 
Discarding the following lemma (unsupported): (S n < S (length l) : Prop)
[Lemma,SMTCoq plugin]
Tactic call ran for 0.093 secs (0.034u,0.011s) (failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName23 Tindex_0)) (= (op_2 op_0 (op_1 SMTCoqRelName23)) (op_2 op_0 SMTCoqRelName23)) ) ).
*)
(* RESULT #163: N/A. Quantified. Rewrite in hyp. *)
     rewrite H0 in H; inversion_clear H as [|? H1]; inversion_clear H1.
   Qed.

End Cutting.

(**************************************************************)
(** ** Combining pairs of lists of possibly-different lengths *)
(**************************************************************)

Section Combining.
    Variables (A B : Type).

    Lemma combine_nil : forall (l : list A),
      combine l (@nil B) = @nil (A*B).
    Proof.
      intros l.
      apply length_zero_iff_nil.
(* GOAL #164 *)
(* assert (length (@nil A) = 0) by admit. (* simpl. *)
assert (Init.Nat.min (length l) 0 = 0) by admit. (* Nat.min_0_r *)
Fail Timeout 20 (time abduce 4).
assert ((Init.Nat.min ((length (A:=A)) l) ((length (A:=A)) [])) = ((length (A:=A * B)) ((combine (A:=A) (B:=B)) l []))).
{ now rewrite combine_length. } smt. *)
(* Anomaly "Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")." *)
(* OUTPUT #164: Tactic call ran for 4.54 secs (0.017u,0.033s) (failure)
Tactic call ran for 5.524 secs (0.006u,0.026s) (failure)
The command has indeed failed with message:
cvc5 returned SAT.
The solver cannot prove the goal, but one of the following hypotheses (printed in Prop, but the corresponding Boolean versions also apply) would make it provable:
((length (A:=A * B)) ((combine (A:=A) (B:=B)) l [])) = 0
((length (A:=A * B)) ((combine (A:=A) (B:=B)) l [])) = ((length (A:=A)) [])
(Init.Nat.min ((length (A:=A)) l) 0) = ((length (A:=A * B)) ((combine (A:=A) (B:=B)) l []))
(Init.Nat.min ((length (A:=A)) l) ((length (A:=A)) [])) = ((length (A:=A * B)) ((combine (A:=A) (B:=B)) l [])) *)
(* RESULT #164: Partial. Poked holes. Abduct is symmetry of rewrite. *)
      rewrite combine_length. simpl.
(* GOAL #165 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #165: 
Tactic call ran for 0.294 secs (0.007u,0.029s) (failure)
The command has indeed failed with message:
cvc5 returned SAT.
The solver cannot prove the goal, but one of the following hypotheses (printed in Prop, but the corresponding Boolean versions also apply) would make it provable:
(Init.Nat.min ((length (A:=A)) l) 0) = 0
*) (* assert ((Init.Nat.min ((length (A:=A)) l) 0) = 0). {
Search (Init.Nat.min _ 0 = 0). apply Nat.min_0_r. } smt. *)
(* RESULT #165: Success. smt fails on Nat goal. *)
      rewrite Nat.min_0_r.
      reflexivity.
    Qed.

    Lemma combine_firstn_l : forall (l : list A) (l' : list B),
      combine l l' = combine l (firstn (length l) l').
    Proof.
      intro l; induction l as [| x l IHl]; intros l'; [reflexivity|].
      destruct l' as [| x' l']; [reflexivity|].
      simpl. specialize IHl with l'. (* verit. admit. admit. admit. admit. *)
(* GOAL #166 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #166: 
The command has not failed!
Tactic call ran for 0.044 secs (0.008u,0.012s) (success)
*)
(* RESULT #166: Smt Success. Local lemma. *)
rewrite <- IHl.
      reflexivity.
    Qed.

    Lemma combine_firstn_r : forall (l : list A) (l' : list B),
      combine l l' = combine (firstn (length l') l) l'.
    Proof.
      intros l l'. generalize dependent l.
      induction l' as [| x' l' IHl']; intros l.
      - simpl. apply combine_nil.
      - destruct l as [| x l]; [reflexivity|].
        simpl. specialize IHl' with l. (* verit. admit. admit. admit. admit. *)
(* GOAL #167 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #167: 
The command has not failed!
Tactic call ran for 0.112 secs (0.031u,0.036s) (success)*)
(* RESULT #167: Smt Success. *)
        rewrite <- IHl'. reflexivity.
    Qed.

    Lemma combine_firstn : forall (l : list A) (l' : list B) (n : nat),
      firstn n (combine l l') = combine (firstn n l) (firstn n l').
    Proof.
      intro l; induction l as [| x l IHl]; intros l' n.
      - simpl. 
(* GOAL #168 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #168: 
Tactic call ran for 4.981 secs (0.011u,0.045s) (failure)
The command has indeed failed with message:
cvc5 returned SAT.
The solver cannot prove the goal, but one of the following hypotheses (printed in Prop, but the corresponding Boolean versions also apply) would make it provable:
((combine (A:=A) (B:=B)) ((firstn (A:=A)) n []) ((firstn (A:=B)) n l')) = ((firstn (A:=A * B)) n [])
*)
(* RESULT #168: Partial. asserts goal symmetry. *)
        rewrite firstn_nil. 
(* GOAL #169 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #169: 
Tactic call ran for 1.047 secs (0.01u,0.02s) (failure)
The command has indeed failed with message:
cvc5 returned SAT.
The solver cannot prove the goal, but one of the following hypotheses (printed in Prop, but the corresponding Boolean versions also apply) would make it provable:
((combine (A:=A) (B:=B)) ((firstn (A:=A)) n []) ((firstn (A:=B)) n l')) = []*)
(* RESULT #169: Partial. asserts goal symmetry. *)
        rewrite firstn_nil. reflexivity.
      - destruct l' as [| x' l'].
        + simpl. 
(* GOAL #170 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #170: 
Tactic call ran for 0.075 secs (0.017u,0.012s) (failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName0 Tindex_1) (SMTCoqRelName1 Tindex_3)) (= (op_2 SMTCoqRelName0 (op_1 op_0 SMTCoqRelName1)) (op_1 (op_3 SMTCoqRelName0 op_0) (op_4 SMTCoqRelName0 SMTCoqRelName1))) ) ).*)
(* RESULT #170: N/A. Quantified. *)
          rewrite firstn_nil.
(* GOAL #171 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #171: 
Tactic call ran for 0.121 secs (0.017u,0.024s) (failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName2 Tindex_1) (SMTCoqRelName3 Tindex_3)) (= (op_2 SMTCoqRelName2 (op_1 op_0 SMTCoqRelName3)) (op_1 (op_3 SMTCoqRelName2 op_0) (op_4 SMTCoqRelName2 SMTCoqRelName3))) ) ).
*)
(* RESULT #171: N/A. Quantified. *)
          rewrite firstn_nil. 
(* GOAL #172 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #172: 
Tactic call ran for 0.08 secs (0.025u,0.015s) (failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName4 Tindex_1) (SMTCoqRelName5 Tindex_3)) (= (op_2 SMTCoqRelName4 (op_1 op_0 SMTCoqRelName5)) (op_1 (op_3 SMTCoqRelName4 op_0) (op_4 SMTCoqRelName4 SMTCoqRelName5))) ) ).
*)
(* RESULT #172: N/A. Quantified. *)
          rewrite combine_nil. reflexivity.
        + simpl. destruct n as [| n]; [reflexivity|].
(* GOAL #173 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #173: 
Tactic call ran for 0.121 secs (0.041u,0.016s) (failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName6 Tindex_1) (SMTCoqRelName7 Tindex_3)) (= (op_2 SMTCoqRelName6 (op_1 op_0 SMTCoqRelName7)) (op_1 (op_3 SMTCoqRelName6 op_0) (op_4 SMTCoqRelName6 SMTCoqRelName7))) ) ).
*)
(* RESULT #173: N/A. Quantified. *)
          rewrite firstn_cons. 
(* GOAL #174 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #174: 
Tactic call ran for 0.077 secs (0.015u,0.012s) (failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName8 Tindex_1) (SMTCoqRelName9 Tindex_3)) (= (op_2 SMTCoqRelName8 (op_1 op_0 SMTCoqRelName9)) (op_1 (op_3 SMTCoqRelName8 op_0) (op_4 SMTCoqRelName8 SMTCoqRelName9))) ) ).
*)
(* RESULT #174: N/A. Quantified. *)
          rewrite firstn_cons. simpl.
(* GOAL #175 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #175: 
Tactic call ran for 0.11 secs (0.034u,0.029s) (failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName10 Tindex_1) (SMTCoqRelName11 Tindex_3)) (= (op_2 SMTCoqRelName10 (op_1 op_0 SMTCoqRelName11)) (op_1 (op_3 SMTCoqRelName10 op_0) (op_4 SMTCoqRelName10 SMTCoqRelName11))) ) ).
*)
(* RESULT #175: N/A. Quantified. Local lemma. *)
          rewrite IHl. reflexivity.
    Qed.

End Combining.

(**********************************************************************)
(** ** Predicate for List addition/removal (no need for decidability) *)
(**********************************************************************)

Section Add.

  Variable A : Type.

  (* [Add a l l'] means that [l'] is exactly [l], with [a] added
     once somewhere *)
  Inductive Add (a:A) : list A -> list A -> Prop :=
    | Add_head l : Add a l (a::l)
    | Add_cons x l l' : Add a l l' -> Add a (x::l) (x::l').

  Lemma Add_app a l1 l2 : Add a (l1++l2) (l1++a::l2).
  Proof.
   induction l1; simpl; now constructor.
  Qed.

  Lemma Add_split a l l' :
    Add a l l' -> exists l1 l2, l = l1++l2 /\ l' = l1++a::l2.
  Proof.
   induction 1 as [l|x ? ? ? IHAdd].
   - exists nil; exists l; split; trivial.
   - destruct IHAdd as (l1 & l2 & Hl & Hl').
     exists (x::l1); exists l2; split; simpl; f_equal; trivial.
  Qed.

  Lemma Add_in a l l' : Add a l l' ->
   forall x, In x l' <-> In x (a::l).
  Proof.
   induction 1 as [|? ? ? ? IHAdd]; intros; simpl in *. 
(* GOAL #176 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #176: 
Tactic call ran for 0.014 secs (0.014u,0.s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #176: N/A. Non-bool predicate. Local lemma. *)
   rewrite ?IHAdd; tauto. 
(* GOAL #177 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #177: 
Tactic call ran for 0.036 secs (0.024u,0.011s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #177: N/A. Non-bool predicate. Local lemma. *)
   rewrite ?IHAdd; tauto.
  Qed.

  Lemma Add_length a l l' : Add a l l' -> length l' = S (length l).
  Proof.
   induction 1; simpl; auto with arith.
  Qed.

  Lemma Add_inv a l : In a l -> exists l', Add a l' l.
  Proof.
   intro Ha. destruct (in_split _ _ Ha) as (l1 & l2 & ->).
   exists (l1 ++ l2). apply Add_app.
  Qed.

  Lemma incl_Add_inv a l u v :
    ~In a l -> incl (a::l) v -> Add a u v -> incl l u.
  Proof.
   intros Ha H AD y Hy.
   assert (Hy' : In y (a::u)).
   { (* GOAL #178 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #178: 
Tactic call ran for 0.009 secs (0.009u,0.s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #178: N/A. Non-bool predicate. Local lemma. *)
rewrite <- (Add_in AD). apply H; simpl; auto. }
   destruct Hy'; [ subst; now elim Ha | trivial ].
  Qed.

End Add.

(********************************)
(** ** Lists without redundancy *)
(********************************)

Section ReDun.

  Variable A : Type.

  Inductive NoDup : list A -> Prop :=
    | NoDup_nil : NoDup nil
    | NoDup_cons : forall x l, ~ In x l -> NoDup l -> NoDup (x::l).

  Lemma NoDup_Add a l l' : Add a l l' -> (NoDup l' <-> NoDup l /\ ~In a l).
  Proof.
   induction 1 as [l|x l l' AD IH].
   - split; [ inversion_clear 1; now split | now constructor ].
   - split.
     + inversion_clear 1.
(* GOAL #179 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #179: 
Tactic call ran for 0.008 secs (0.u,0.007s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #179: N/A. Non-bool predicate. Local lemma. Rewrite in hyp. *)
rewrite IH in *. 
(* GOAL #180 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #180: 
Tactic call ran for 0.014 secs (0.006u,0.007s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #180: N/A. Non-bool predicate. Local lemma.*)
rewrite (Add_in AD) in *.
       simpl in *; split; try constructor; intuition.
     + intros (N,IN). inversion_clear N. constructor.
       * (* GOAL #181 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #181: 
Tactic call ran for 0.125 secs (0.078u,0.043s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #181: N/A. Non-bool predicate. Local lemma. Rewrite in hyp. *)
rewrite (Add_in AD); simpl in *; intuition.
       * apply IH. split; trivial. simpl in *; intuition.
  Qed.

  Lemma NoDup_remove l l' a :
    NoDup (l++a::l') -> NoDup (l++l') /\ ~In a (l++l').
  Proof.
  apply NoDup_Add. apply Add_app.
  Qed.

  Lemma NoDup_remove_1 l l' a : NoDup (l++a::l') -> NoDup (l++l').
  Proof.
  intros. now apply NoDup_remove with a.
  Qed.

  Lemma NoDup_remove_2 l l' a : NoDup (l++a::l') -> ~In a (l++l').
  Proof.
  intros. now apply NoDup_remove.
  Qed.

  Theorem NoDup_cons_iff a l:
    NoDup (a::l) <-> ~ In a l /\ NoDup l.
  Proof.
    split.
    + inversion_clear 1. now split.
    + now constructor.
  Qed.

  Lemma NoDup_rev l : NoDup l -> NoDup (rev l).
  Proof.
    induction l as [|a l IHl]; simpl; intros Hnd; [ constructor | ].
    inversion_clear Hnd as [ | ? ? Hnin Hndl ].
    assert (Add a (rev l) (rev l ++ a :: nil)) as Hadd. {
(* GOAL #182 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #182: 
Tactic call ran for 0.009 secs (0.009u,0.s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #182: N/A. Non-bool predicate. *)
      rewrite <- (app_nil_r (rev l)) at 1. apply Add_app. }
    apply NoDup_Add in Hadd; apply Hadd; intuition.
    now apply Hnin, in_rev.
  Qed.

  Lemma NoDup_filter f l : NoDup l -> NoDup (filter f l).
  Proof.
    induction l as [|a l IHl]; simpl; intros Hnd; auto.
    apply NoDup_cons_iff in Hnd.
    destruct (f a); [ | intuition ].
    apply NoDup_cons_iff; split; [intro H|]; intuition.
    apply filter_In in H; intuition.
  Qed.

  (** Effective computation of a list without duplicates *)

  Hypothesis decA: forall x y : A, {x = y} + {x <> y}.

  Fixpoint nodup (l : list A) : list A :=
    match l with
      | [] => []
      | x::xs => if in_dec decA x xs then nodup xs else x::(nodup xs)
    end.

  Lemma nodup_fixed_point (l : list A) :
    NoDup l -> nodup l = l.
  Proof.
    induction l as [| x l IHl]; [auto|]. intros H.
    simpl. destruct (in_dec decA x l) as [Hx | Hx].
    - (* GOAL #183 *) (* Fail Timeout 20 (time abduce 22). *)
(* OUTPUT #183: 
Discarding the following lemma (unsupported): (In x l : Prop)
[Lemma,SMTCoq plugin]
Discarding the following lemma (unsupported): (NoDup (x :: l) : Prop)
[Lemma,SMTCoq plugin]
Tactic call ran for 8.355 secs (0.034u,0.025s) (failure)
The command has indeed failed with message:
cvc5 returned SAT.
The solver cannot prove the goal, but one of the following hypotheses (printed in Prop, but the corresponding Boolean versions also apply) would make it provable:
(cons x l) = l
(cons x (nodup l)) = l
(cons x l) = (nodup l)
(nodup (nodup l)) = (cons x l)
(cons x (nodup l)) = (nodup l)
(cons x (nodup (nodup l))) = l
(cons x (nodup (nodup (nodup l)))) = l
(cons x (nodup (nodup l))) = (nodup l)
(cons x (nodup l)) = (nodup (nodup l))
(nodup (nodup (nodup l))) = (cons x l)
(nodup (nodup (nodup (nodup l)))) = (cons x l)
(cons x (nodup (nodup (nodup l)))) = (nodup l)
(cons x (nodup (nodup l))) = (nodup (nodup l))
(cons x (nodup (nodup (nodup (nodup l))))) = l
(nodup (nodup (nodup l))) = (cons x (nodup l))
(nodup (nodup (nodup (nodup l)))) = (cons x (nodup l))
(nodup (nodup (nodup (nodup (nodup l))))) = (cons x l)
(cons x (nodup (nodup (nodup (nodup l))))) = (nodup l)
(cons x (nodup (nodup (nodup (nodup (nodup l)))))) = l
(cons x (nodup (nodup (nodup l)))) = (nodup (nodup l))
(nodup (nodup (nodup l))) = (cons x (nodup (nodup l)))
(not (not (cons x l) = l) && (nodup l) = l)
*)
(* RESULT #183: Failure. Drops lemma. Can't poke holes. Rewrite in hyp. *)rewrite NoDup_cons_iff in H. destruct H as [H' _]. contradiction.
    - (* verit. *) (* GOAL #184 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #184: 
The command has not failed!
Discarding the following lemma (unsupported): (~ In x l : Prop)
[Lemma,SMTCoq plugin]
Discarding the following lemma (unsupported): (NoDup (x :: l) : Prop)
[Lemma,SMTCoq plugin]
Tactic call ran for 0.076 secs (0.032u,0.016s) (success)
*)
(* RESULT #184: Smt Success. Drops lemma. Rewrite in hyp. *) rewrite NoDup_cons_iff in H. destruct H as [_ H']. apply IHl in H'. 
(* GOAL #185 *) (* Fail Timeout 20 (time abduce 3). *)
(* OUTPUT #185: 
Discarding the following lemma (unsupported): (NoDup l -> nodup l = l)
[Lemma,SMTCoq plugin]
Discarding the following lemma (unsupported): (~ In x l)
[Lemma,SMTCoq plugin]
Discarding the following lemma (unsupported): (nodup l = l)
[Lemma,SMTCoq plugin]
Tactic call ran for 0.611 secs (0.011u,0.016s) (failure)
The command has indeed failed with message:
cvc5 returned SAT.
The solver cannot prove the goal, but one of the following hypotheses (printed in Prop, but the corresponding Boolean versions also apply) would make it provable:
(nodup l) = l
(cons x (nodup l)) = (cons x l)
*)
(* RESULT #185: Success. Local lemma. smt fails on non-bool goal. *)
rewrite -> H'. reflexivity.
  Qed.

  Lemma nodup_In l x : In x (nodup l) <-> In x l.
  Proof.
    induction l as [|a l' Hrec]; simpl.
    - reflexivity.
    - destruct (in_dec decA a l'); simpl. 
      * (* GOAL #186 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #186: 
Tactic call ran for 0.03 secs (0.026u,0.004s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #186: N/A. Non-bool predicate. *)rewrite Hrec. intuition; now subst.
      * (* GOAL #187 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #187: 
Tactic call ran for 0.02 secs (0.012u,0.008s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #187: N/A. Non-bool predicate. *)
rewrite Hrec. reflexivity.
  Qed.

  Lemma nodup_incl l1 l2 : incl l1 (nodup l2) <-> incl l1 l2.
  Proof.
    split; intros Hincl a Ha; apply nodup_In; intuition.
  Qed.

  Lemma NoDup_nodup l: NoDup (nodup l).
  Proof.
    induction l as [|a l' Hrec]; simpl.
    - constructor.
    - destruct (in_dec decA a l'); simpl.
      * assumption.
      * constructor. 
(* GOAL #188 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #188: 
Tactic call ran for 0.004 secs (0.004u,0.s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #188: N/A. Non-bool predicate. *)
now rewrite nodup_In. assumption.
  Qed.

  Lemma nodup_inv k l a : nodup k = a :: l -> ~ In a l.
  Proof.
    intros H.
    assert (H' : NoDup (a::l)).
    { (* GOAL #189 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #189: 
Tactic call ran for 0.01 secs (0.006u,0.003s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #189: N/A. Non-bool predicate. Local lemma. *) rewrite <- H. apply NoDup_nodup. }
    now inversion_clear H'.
  Qed.

  Theorem NoDup_count_occ l:
    NoDup l <-> (forall x:A, count_occ decA l x <= 1).
  Proof.
    induction l as [| a l' Hrec].
    - simpl; split; auto. constructor.
    - (* GOAL #190 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #190: 
Tactic call ran for 0.003 secs (0.003u,0.s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #190: N/A. Non-bool predicate. *)rewrite NoDup_cons_iff. 
(* GOAL #191 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #191: 
Tactic call ran for 0.003 secs (0.003u,0.s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #191: N/A. Non-bool predicate. *)
rewrite Hrec. 
(* GOAL #192 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #192: 
Tactic call ran for 0.003 secs (0.003u,0.s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #192: N/A. Non-bool predicate. *)
rewrite (count_occ_not_In decA). clear Hrec. split.
      + intros (Ha, H) x. simpl. destruct (decA a x); auto.
        subst. (* GOAL #193 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #193: 
Tactic call ran for 0.026 secs (0.018u,0.007s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #193: N/A. Non-bool predicate. Local lemma. *)
 now rewrite Ha.
      + intro H; split.
        * specialize (H a). 
(* GOAL #194 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #194: 
Discarding the following lemma (unsupported): (count_occ decA (a :: l') a <= 1 : Prop)
[Lemma,SMTCoq plugin]
Tactic call ran for 0.218 secs (0.016u,0.036s) (failure)
The command has indeed failed with message:
cvc5 returned SAT.
The solver cannot prove the goal, but one of the following hypotheses (printed in Prop, but the corresponding Boolean versions also apply) would make it provable:
((count_occ (A:=A)) decA l' a) = 0
*)
(* RESULT #194: Failure. Drops nat lemma. Can't poke holes. asserts goal. *)
          rewrite count_occ_cons_eq in H; trivial.
          now inversion H.
        * intros x. specialize (H x). simpl in *. destruct (decA a x); auto.
          now apply Nat.lt_le_incl.
  Qed.

  Theorem NoDup_count_occ' l:
    NoDup l <-> (forall x:A, In x l -> count_occ decA l x = 1).
  Proof.
(* GOAL #195 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #195: 
Tactic call ran for 0.002 secs (0.u,0.002s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #195: N/A. Non-bool predicate. *)
    rewrite NoDup_count_occ.
    setoid_rewrite (count_occ_In decA). unfold gt, lt in *.
    split; intros H x; specialize (H x);
    set (n := count_occ decA l x) in *; clearbody n.
    (* the rest would be solved by omega if we had it here... *)
    - now apply Nat.le_antisymm.
    - destruct (Nat.le_gt_cases 1 n); trivial.
      + (* GOAL #196 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #196: 
Tactic call ran for 0.025 secs (0.025u,0.s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #196: N/A. Non-bool predicate. Local lemma. *)rewrite H; trivial.
      + now apply Nat.lt_le_incl.
  Qed.

  (** Alternative characterisations of being without duplicates,
      thanks to [nth_error] and [nth] *)

  Lemma NoDup_nth_error l :
    NoDup l <->
    (forall i j, i<length l -> nth_error l i = nth_error l j -> i = j).
  Proof.
    split.
    { intros H; induction H as [|a l Hal Hl IH]; intros i j Hi E.
      - inversion Hi.
      - destruct i, j; simpl in *; auto.
        * elim Hal. eapply nth_error_In; eauto.
        * elim Hal. eapply nth_error_In; eauto.
        * f_equal. apply IH; auto with arith. }
    { induction l as [|a l IHl]; intros H; constructor.
      * intro Ha. apply In_nth_error in Ha. destruct Ha as (n,Hn).
        assert (n < length l). {
(* GOAL #197 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #197: 
Tactic call ran for 0.114 secs (0.081u,0.032s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #197: N/A. Non-bool predicate. *)
  rewrite <- nth_error_Some. 
(* GOAL #198 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #198: 
Discarding the following lemma (unsupported): ((forall i j : nat, i < length l -> nth_error l i = nth_error l j -> i = j) ->
 NoDup l)
[Lemma,SMTCoq plugin]
Tactic call ran for 0.136 secs (0.076u,0.023s) (failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName31 Tindex_3) (SMTCoqRelName32 Tindex_3)) (or (not (= (op_2 (op_5 op_3 op_0) SMTCoqRelName32) (op_2 (op_5 op_3 op_0) SMTCoqRelName31))) (= SMTCoqRelName31 SMTCoqRelName32)) ) ).
*)
(* RESULT #198: N/A. Quantified. Local lemma. *)
  now rewrite Hn. }
        specialize (H 0 (S n)). simpl in H. discriminate H; auto with arith.
      * apply IHl.
        intros i j Hi E. apply eq_add_S, H; simpl; auto with arith. }
  Qed.

  Lemma NoDup_nth l d :
    NoDup l <->
    (forall i j, i<length l -> j<length l ->
       nth i l d = nth j l d -> i = j).
  Proof.
    split.
    { intros H; induction H as [|a l Hal Hl IH]; intros i j Hi Hj E.
      - inversion Hi.
      - destruct i, j; simpl in *; auto.
        * elim Hal. subst a. apply nth_In; auto with arith.
        * elim Hal. subst a. apply nth_In; auto with arith.
        * f_equal. apply IH; auto with arith. }
    { induction l as [|a l IHl]; intros H; constructor.
      * intro Ha. eapply In_nth in Ha. destruct Ha as (n & Hn & Hn').
        specialize (H 0 (S n)). simpl in H. discriminate H; eauto with arith.
      * apply IHl.
        intros i j Hi Hj E. apply eq_add_S, H; simpl; auto with arith. }
  Qed.

  (** Having [NoDup] hypotheses bring more precise facts about [incl]. *)

  Lemma NoDup_incl_length l l' :
    NoDup l -> incl l l' -> length l <= length l'.
  Proof.
   intros N. revert l'. induction N as [|a l Hal N IH]; simpl.
   - auto with arith.
   - intros l' H.
     destruct (Add_inv a l') as (l'', AD). { apply H; simpl; auto. }
(* GOAL #199 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #199: 
Tactic call ran for 0.015 secs (0.015u,0.s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #199: N/A. Non-bool predicate. *)
     rewrite (Add_length AD). apply le_n_S. apply IH.
     now apply incl_Add_inv with a l'.
  Qed.

  Lemma NoDup_length_incl l l' :
    NoDup l -> length l' <= length l -> incl l l' -> incl l' l.
  Proof.
   intros N. revert l'. induction N as [|a l Hal N IH].
   - intro l'; destruct l'; easy.
   - intros l' E H x Hx.
     destruct (Add_inv a l') as (l'', AD). { apply H; simpl; auto. }
(* GOAL #200 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #200: 
Tactic call ran for 0.012 secs (0.011u,0.s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #200: N/A. Non-bool predicate. *)
     rewrite (Add_in AD) in Hx. simpl in Hx.
     destruct Hx as [Hx|Hx]; [left; trivial|right].
     revert x Hx. apply (IH l''); trivial.
     * apply le_S_n. (* GOAL #201 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #201: 
Tactic call ran for 0.013 secs (0.013u,0.s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #201: N/A. Non-bool predicate. *)now rewrite <- (Add_length AD).
     * now apply incl_Add_inv with a l'.
  Qed.

  Lemma NoDup_incl_NoDup (l l' : list A) : NoDup l ->
    length l' <= length l -> incl l l' -> NoDup l'.
  Proof.
    revert l'; induction l as [|a l IHl]; simpl; intros l' Hnd Hlen Hincl.
    - now destruct l'; inversion Hlen.
    - assert (In a l') as Ha by now apply Hincl; left.
      apply in_split in Ha as [l1' [l2' ->]].
      inversion_clear Hnd as [|? ? Hnin Hnd'].
      apply (NoDup_Add (Add_app a l1' l2')); split.
      + apply IHl; auto.
        * (* GOAL #202 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #202: 
Tactic call ran for 0.025 secs (0.025u,0.s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #202: N/A. Non-bool predicate. *)
          rewrite app_length.
(* GOAL #203 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #203: 
Tactic call ran for 0.01 secs (0.01u,0.s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #203: N/A. Non-bool predicate. Rewrite in hyp. *)
          rewrite app_length in Hlen; simpl in Hlen.
(* GOAL #204 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #204: 
Tactic call ran for 0.015 secs (0.015u,0.s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #204: N/A. Non-bool predicate. Rewrite in hyp. *)
          rewrite Nat.add_succ_r in Hlen.
          now apply Nat.succ_le_mono.
        * apply (incl_Add_inv (u:= l1' ++ l2')) in Hincl; auto.
          apply Add_app.
      + intros Hnin'.
        assert (incl (a :: l) (l1' ++ l2')) as Hincl''.
        { apply incl_tran with (l1' ++ a :: l2'); auto.
          intros x Hin.
          apply in_app_or in Hin as [Hin|[->|Hin]]; intuition. }
        apply NoDup_incl_length in Hincl''; [ | now constructor ].
        apply (Nat.nle_succ_diag_l (length l1' + length l2')).
(* GOAL #205 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #205: 
Tactic call ran for 0.014 secs (0.014u,0.s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #205: N/A. Non-bool predicate. *)
        rewrite_all app_length. simpl in Hlen. 
(* GOAL #206 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #206: 
Tactic call ran for 0.035 secs (0.031u,0.003s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #206: N/A. Non-bool predicate. rewrite in hyp. *)
        rewrite Nat.add_succ_r in Hlen.
        now transitivity (S (length l)).
  Qed.

End ReDun.

(** NoDup and map *)

(** NB: the reciprocal result holds only for injective functions,
    see FinFun.v *)

Lemma NoDup_map_inv A B (f:A->B) l : NoDup (map f l) -> NoDup l.
Proof.
 induction l; simpl; inversion_clear 1; subst; constructor; auto.
 intro H. now apply (in_map f) in H.
Qed.

(***********************************)
(** ** Sequence of natural numbers *)
(***********************************)

Section NatSeq.

  (** [seq] computes the sequence of [len] contiguous integers
      that starts at [start]. For instance, [seq 2 3] is [2::3::4::nil]. *)

  Fixpoint seq (start len:nat) : list nat :=
    match len with
      | 0 => nil
      | S len => start :: seq (S start) len
    end.

  Lemma cons_seq : forall len start, start :: seq (S start) len = seq start (S len).
  Proof.
    reflexivity.
  Qed.

  Lemma seq_length : forall len start, length (seq start len) = len.
  Proof.
    intro len; induction len; simpl; auto.
  Qed.

  Lemma seq_nth : forall len start n d,
    n < len -> nth n (seq start len) d = start+n.
  Proof.
    intro len; induction len as [|len IHlen]; intros start n d H.
    inversion H.
    simpl seq.
    destruct n; simpl.
    auto with arith.
(* GOAL #207 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #207: 
Discarding the following lemma (unsupported): (S n < S len : Prop)
[Lemma,SMTCoq plugin]
Tactic call ran for 0.142 secs (0.045u,0.032s) (failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName2 Tindex_0) (SMTCoqRelName3 Tindex_0) (SMTCoqRelName4 Tindex_0)) (= (op_2 SMTCoqRelName3 (op_1 SMTCoqRelName4 op_0) SMTCoqRelName2) (op_3 SMTCoqRelName4 SMTCoqRelName3)) ) ).
*)
(* RESULT #207: N/A. Quantified. Local lemma. *)
    rewrite IHlen;simpl; auto with arith.
  Qed.

  Lemma seq_shift : forall len start,
    map S (seq start len) = seq (S start) len.
  Proof.
    intro len; induction len as [|len IHlen]; simpl; auto.
    intros.
(* GOAL #208 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #208: 
Tactic call ran for 0.071 secs (0.039u,0.031s) (failure)
The command has indeed failed with message:
Anomaly "Uncaught exception Invalid_argument("index out of bounds")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #208: N/A. Out of bounds. *)
    rewrite IHlen.
    auto with arith.
  Qed.

  Lemma in_seq len start n :
    In n (seq start len) <-> start <= n < start+len.
  Proof.
   revert start. induction len as [|len IHlen]; simpl; intros.
   - (* GOAL #209 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #209: 
Tactic call ran for 0.005 secs (0.005u,0.s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #209: N/A. Non-bool predicate. *) rewrite <- plus_n_O. split;[easy|].
     intros (H,H'). apply (Lt.lt_irrefl _ (Lt.le_lt_trans _ _ _ H H')).
   - (* GOAL #210 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #210: 
Tactic call ran for 0.023 secs (0.022u,0.s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #210: N/A. Non-bool predicate. Local lemma. *)
    rewrite IHlen.
(* GOAL #211 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #211: 
Tactic call ran for 0.018 secs (0.018u,0.s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #211: N/A. Non-bool predicate. *)
    rewrite<- plus_n_Sm; simpl; split.
     + intros [H|H]; subst; intuition auto with arith.
     + intros (H,H'). destruct (Lt.le_lt_or_eq _ _ H); intuition.
  Qed.

  Lemma seq_NoDup len start : NoDup (seq start len).
  Proof.
   revert start; induction len; simpl; constructor; trivial.
(* GOAL #212 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #212: 
Tactic call ran for 0.004 secs (0.004u,0.s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #212: N/A. Non-bool predicate. *)
   rewrite in_seq. intros (H,_). apply (Lt.lt_irrefl _ H).
  Qed.

  Lemma seq_app : forall len1 len2 start,
    seq start (len1 + len2) = seq start len1 ++ seq (start + len1) len2.
  Proof.
    intro len1; induction len1 as [|len1' IHlen]; intros; simpl in *.
    - (* GOAL #213 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #213: 
Tactic call ran for 0.324 secs (0.008u,0.04s) (failure)
The command has indeed failed with message:
cvc5 returned SAT.
The solver cannot prove the goal, but one of the following hypotheses (printed in Prop, but the corresponding Boolean versions also apply) would make it provable:
(Init.Nat.add start 0) = start*)
(* assert ((Init.Nat.add start 0) = start). { Search (_ + 0 = _). apply Nat.add_0_r. } smt. *)
(* RESULT #213: Success. *) now rewrite Nat.add_0_r.
    - (* GOAL #214 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #214: 
Tactic call ran for 0.109 secs (0.023u,0.023s) (failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName6 Tindex_1) (SMTCoqRelName7 Tindex_1)) (= (op_2 SMTCoqRelName6 (op_1 op_0 SMTCoqRelName7)) (op_3 (op_2 SMTCoqRelName6 op_0) (op_2 (op_1 SMTCoqRelName6 op_0) SMTCoqRelName7))) ) ).
*)
(* RESULT #214: N/A. Quantified. *)rewrite Nat.add_succ_r. 
(* GOAL #215 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #215: 
Tactic call ran for 0.074 secs (0.011u,0.008s) (failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName8 Tindex_1) (SMTCoqRelName9 Tindex_1)) (= (op_2 SMTCoqRelName8 (op_1 op_0 SMTCoqRelName9)) (op_3 (op_2 SMTCoqRelName8 op_0) (op_2 (op_1 SMTCoqRelName8 op_0) SMTCoqRelName9))) ) ).
*)
(* RESULT #215: N/A. Quantified. Local lemma. *)
rewrite IHlen. easy.
  Qed.

  Lemma seq_S : forall len start, seq start (S len) = seq start len ++ [start + len].
  Proof.
   intros len start.
   change [start + len] with (seq (start + len) 1).
(* GOAL #216 *) 
(* assert (len + 1 = S (len + 0)) by admit. (* plus_n_Sm *)
assert (len + 0 = len) by admit. (* plus_n_O *)
Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #216: The command has indeed failed with message:
Timeout!*)
(* RESULT #216: Failure. Poked holes. *)
   rewrite <- seq_app.
(* GOAL #217 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #217: 
Tactic call ran for 7.069 secs (0.009u,0.023s) (failure)
The command has indeed failed with message:
cvc5 returned SAT.
The solver cannot prove the goal, but one of the following hypotheses (printed in Prop, but the corresponding Boolean versions also apply) would make it provable:
(Init.Nat.add len (S 0)) = (S len)
*)
(* assert ((Init.Nat.add len (S 0)) = (S len)). { Search (_ + 1 = S _).
apply Nat.add_1_r. } smt. *)
(* RESULT #217: Success. *)
   rewrite <- plus_n_Sm.

(* GOAL #218 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #218: 
Tactic call ran for 0.273 secs (0.007u,0.028s) (failure)
The command has indeed failed with message:
cvc5 returned SAT.
The solver cannot prove the goal, but one of the following hypotheses (printed in Prop, but the corresponding Boolean versions also apply) would make it provable:
(Init.Nat.add len 0) = len
*) 
(*assert ((Init.Nat.add len 0) = len). { Search (_ + 0 = _).
apply Nat.add_0_r. } smt.*)
(* RESULT #218: Success. *) 
   rewrite <- plus_n_O; reflexivity.
  Qed.

End NatSeq.

Section Exists_Forall.

  (** * Existential and universal predicates over lists *)

  Variable A:Type.

  Section One_predicate.

    Variable P:A->Prop.

    Inductive Exists : list A -> Prop :=
      | Exists_cons_hd : forall x l, P x -> Exists (x::l)
      | Exists_cons_tl : forall x l, Exists l -> Exists (x::l).

    #[local]
    Hint Constructors Exists : core.

    Lemma Exists_exists (l:list A) :
      Exists l <-> (exists x, In x l /\ P x).
    Proof.
      split.
      - induction 1; firstorder.
      - induction l; firstorder; subst; auto.
    Qed.

    Lemma Exists_nth l :
      Exists l <-> exists i d, i < length l /\ P (nth i l d).
    Proof.
      split.
      - intros HE; apply Exists_exists in HE.
        destruct HE as [a [Hin HP]].
        apply (In_nth _ _ a) in Hin; destruct Hin as [i [Hl Heq]].
(* GOAL #219 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #219: 
Tactic call ran for 0.007 secs (0.007u,0.s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #219: N/A. Non-bool predicate. Quantified. *)
        rewrite <- Heq in HP.
        now exists i; exists a.
      - intros [i [d [Hl HP]]].
        apply Exists_exists; exists (nth i l d); split.
        apply nth_In; assumption.
        assumption.
    Qed.

    Lemma Exists_nil : Exists nil <-> False.
    Proof. split; inversion 1. Qed.

    Lemma Exists_cons x l:
      Exists (x::l) <-> P x \/ Exists l.
    Proof. split; inversion 1; auto. Qed.

    Lemma Exists_app l1 l2 :
      Exists (l1 ++ l2) <-> Exists l1 \/ Exists l2.
    Proof.
      induction l1; simpl; split; intros HE; try now intuition.
      - inversion_clear HE; intuition.
      - destruct HE as [HE|HE]; intuition.
        inversion_clear HE; intuition.
    Qed.

    Lemma Exists_rev l : Exists l -> Exists (rev l).
    Proof.
      induction l; intros HE; intuition.
      inversion_clear HE; simpl; apply Exists_app; intuition.
    Qed.

    Lemma Exists_dec l:
      (forall x:A, {P x} + { ~ P x }) ->
      {Exists l} + {~ Exists l}.
    Proof.
      intro Pdec. induction l as [|a l' Hrec].
      - right. (* GOAL #220 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #220: 
Tactic call ran for 0.001 secs (0.001u,0.s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #220: N/A. Non-bool predicate. *)rewrite Exists_nil. easy.
      - destruct Hrec as [Hl'|Hl'].
        + left. now apply Exists_cons_tl.
        + destruct (Pdec a) as [Ha|Ha].
          * left. now apply Exists_cons_hd.
          * right. abstract now inversion 1.
    Defined.

    Lemma Exists_fold_right l :
      Exists l <-> fold_right (fun x => or (P x)) False l.
    Proof.
      induction l; simpl; split; intros HE; try now inversion HE; intuition.
    Qed.

    Lemma incl_Exists l1 l2 : incl l1 l2 -> Exists l1 -> Exists l2.
    Proof.
      intros Hincl HE.
      apply Exists_exists in HE; destruct HE as [a [Hin HP]].
      apply Exists_exists; exists a; intuition.
    Qed.

    Inductive Forall : list A -> Prop :=
      | Forall_nil : Forall nil
      | Forall_cons : forall x l, P x -> Forall l -> Forall (x::l).

    #[local]
    Hint Constructors Forall : core.

    Lemma Forall_forall (l:list A):
      Forall l <-> (forall x, In x l -> P x).
    Proof.
      split.
      - induction 1; firstorder; subst; auto.
      - induction l; firstorder auto with datatypes.
    Qed.

    Lemma Forall_nth l :
      Forall l <-> forall i d, i < length l -> P (nth i l d).
    Proof.
      split.
      - intros HF i d Hl.
        apply (Forall_forall l).
        assumption.
        apply nth_In; assumption.
      - intros HF.
        apply Forall_forall; intros a Hin.
        apply (In_nth _ _ a) in Hin; destruct Hin as [i [Hl Heq]].
(* GOAL #221 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #221: 
Tactic call ran for 0.025 secs (0.024u,0.s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #221: N/A. Non-bool predicate. *)
        rewrite <- Heq; intuition.
    Qed.

    Lemma Forall_inv : forall (a:A) l, Forall (a :: l) -> P a.
    Proof.
      intros a l H; inversion H; trivial.
    Qed.

    Theorem Forall_inv_tail : forall (a:A) l, Forall (a :: l) -> Forall l.
    Proof.
      intros a l H; inversion H; trivial.
    Qed.

    Lemma Forall_app l1 l2 :
      Forall (l1 ++ l2) <-> Forall l1 /\ Forall l2.
    Proof.
      induction l1; simpl; split; intros HF; try now intuition.
      - inversion_clear HF; intuition.
      - destruct HF as [HF1 HF2]; inversion HF1; intuition.
    Qed.

    Lemma Forall_elt a l1 l2 : Forall (l1 ++ a :: l2) -> P a.
    Proof.
      intros HF; apply Forall_app in HF; destruct HF as [HF1 HF2]; now inversion HF2.
    Qed.

    Lemma Forall_rev l : Forall l -> Forall (rev l).
    Proof.
      induction l; intros HF; intuition.
      inversion_clear HF; simpl; apply Forall_app; intuition.
    Qed.

    Lemma Forall_rect : forall (Q : list A -> Type),
      Q [] -> (forall b l, P b -> Q (b :: l)) -> forall l, Forall l -> Q l.
    Proof.
      intros Q H H' l; induction l; intro; [|eapply H', Forall_inv]; eassumption.
    Qed.

    Lemma Forall_dec :
      (forall x:A, {P x} + { ~ P x }) ->
      forall l:list A, {Forall l} + {~ Forall l}.
    Proof.
      intros Pdec l. induction l as [|a l' Hrec].
      - left. apply Forall_nil.
      - destruct Hrec as [Hl'|Hl'].
        + destruct (Pdec a) as [Ha|Ha].
          * left. now apply Forall_cons.
          * right. abstract now inversion 1.
        + right. abstract now inversion 1.
    Defined.

    Lemma Forall_fold_right l :
      Forall l <-> fold_right (fun x => and (P x)) True l.
    Proof.
      induction l; simpl; split; intros HF; try now inversion HF; intuition.
    Qed.

    Lemma incl_Forall l1 l2 : incl l2 l1 -> Forall l1 -> Forall l2.
    Proof.
      intros Hincl HF.
      apply Forall_forall; intros a Ha.
      apply (Forall_forall l1); intuition.
    Qed.

  End One_predicate.

  Lemma map_ext_Forall B : forall (f g : A -> B) l,
    Forall (fun x => f x = g x) l -> map f l = map g l.
  Proof.
    intros; apply map_ext_in, Forall_forall; assumption.
  Qed.

  Theorem Exists_impl : forall (P Q : A -> Prop), (forall a : A, P a -> Q a) ->
    forall l, Exists P l -> Exists Q l.
  Proof.
    intros P Q H l H0.
    induction H0 as [x l H0|x l H0 IHExists].
    apply (Exists_cons_hd Q x l (H x H0)).
    apply (Exists_cons_tl x IHExists).
  Qed.

  Lemma Exists_or : forall (P Q : A -> Prop) l,
    Exists P l \/ Exists Q l -> Exists (fun x => P x \/ Q x) l.
  Proof.
    intros P Q l; induction l as [|a l IHl]; intros [H | H]; inversion H; subst.
    1,3: apply Exists_cons_hd; auto.
    all: apply Exists_cons_tl, IHl; auto.
  Qed.

  Lemma Exists_or_inv : forall (P Q : A -> Prop) l,
    Exists (fun x => P x \/ Q x) l -> Exists P l \/ Exists Q l.
  Proof.
    intros P Q l; induction l as [|a l IHl];
     intro Hl; inversion Hl as [ ? ? H | ? ? H ]; subst.
    - inversion H; now repeat constructor.
    - destruct (IHl H); now repeat constructor.
  Qed.

  Lemma Forall_impl : forall (P Q : A -> Prop), (forall a, P a -> Q a) ->
    forall l, Forall P l -> Forall Q l.
  Proof.
    intros P Q H l. (* GOAL #222 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #222: 
Tactic call ran for 0.004 secs (0.004u,0.s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #222: N/A. Non-bool predicate. *)rewrite !Forall_forall. firstorder.
  Qed.

  Lemma Forall_and : forall (P Q : A -> Prop) l,
    Forall P l -> Forall Q l -> Forall (fun x => P x /\ Q x) l.
  Proof.
    intros P Q l; induction l; intros HP HQ; constructor; inversion HP; inversion HQ; auto.
  Qed.

  Lemma Forall_and_inv : forall (P Q : A -> Prop) l,
    Forall (fun x => P x /\ Q x) l -> Forall P l /\ Forall Q l.
  Proof.
    intros P Q l; induction l; intro Hl; split; constructor; inversion Hl; firstorder.
  Qed.

  Lemma Forall_Exists_neg (P:A->Prop)(l:list A) :
    Forall (fun x => ~ P x) l <-> ~(Exists P l).
  Proof.
(* GOAL #223 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #223: 
Tactic call ran for 0.001 secs (0.001u,0.s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #223: N/A. Non-bool predicate. *)
    rewrite Forall_forall.
(* GOAL #224 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #224: 
Tactic call ran for 0. secs (0.u,0.s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #224: N/A. Non-bool predicate. *) 
    rewrite Exists_exists. firstorder.
  Qed.

  Lemma Exists_Forall_neg (P:A->Prop)(l:list A) :
    (forall x, P x \/ ~P x) ->
    Exists (fun x => ~ P x) l <-> ~(Forall P l).
  Proof.
    intro Dec.
    split.
    - (* GOAL #225 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #225: 
Tactic call ran for 0.003 secs (0.003u,0.s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #225: N/A. Non-bool predicate. *)
rewrite Forall_forall. 
(* GOAL #226 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #226: 
Tactic call ran for 0.011 secs (0.01u,0.s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #226: N/A. Non-bool predicate. *)
rewrite Exists_exists; firstorder.
    - intros NF.
      induction l as [|a l IH].
      + destruct NF. constructor.
      + destruct (Dec a) as [Ha|Ha].
        * apply Exists_cons_tl, IH. contradict NF. now constructor.
        * now apply Exists_cons_hd.
  Qed.

  Lemma neg_Forall_Exists_neg (P:A->Prop) (l:list A) :
    (forall x:A, {P x} + { ~ P x }) ->
    ~ Forall P l ->
    Exists (fun x => ~ P x) l.
  Proof.
    intro Dec.
    apply Exists_Forall_neg; intros x.
    destruct (Dec x); auto.
  Qed.

  Lemma Forall_Exists_dec (P:A->Prop) :
    (forall x:A, {P x} + { ~ P x }) ->
    forall l:list A,
    {Forall P l} + {Exists (fun x => ~ P x) l}.
  Proof.
    intros Pdec l.
    destruct (Forall_dec P Pdec l); [left|right]; trivial.
    now apply neg_Forall_Exists_neg.
  Defined.

  Lemma incl_Forall_in_iff l l' :
    incl l l' <-> Forall (fun x => In x l') l.
  Proof. (* GOAL #227 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #227: 
Tactic call ran for 0.001 secs (0.001u,0.s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #227: N/A. Non-bool predicate. *)now rewrite Forall_forall; split. Qed.

End Exists_Forall.

#[global]
Hint Constructors Exists : core.
#[global]
Hint Constructors Forall : core.

Lemma exists_Forall A B : forall (P : A -> B -> Prop) l,
  (exists k, Forall (P k) l) -> Forall (fun x => exists k, P k x) l.
Proof.
  intros P l; induction l as [|a l IHl]; intros [k HF]; constructor; inversion_clear HF.
  - now exists k.
  - now apply IHl; exists k.
Qed.

Lemma Forall_image A B : forall (f : A -> B) l,
  Forall (fun y => exists x, y = f x) l <-> exists l', l = map f l'.
Proof.
  intros f l; induction l as [|a l IHl]; split; intros HF.
  - exists nil; reflexivity.
  - constructor.
  - inversion_clear HF as [| ? ? [x Hx] HFtl]; subst.
    destruct (proj1 IHl HFtl) as [l' Heq]; subst.
    now exists (x :: l').
  - destruct HF as [l' Heq].
    symmetry in Heq; apply map_eq_cons in Heq.
    destruct Heq as (x & tl & ? & ? & ?); subst.
    constructor.
    + now exists x.
    + now apply IHl; exists tl.
Qed.

Lemma concat_nil_Forall A : forall (l : list (list A)),
  concat l = nil <-> Forall (fun x => x = nil) l.
Proof.
  intro l; induction l as [|a l IHl]; simpl; split; intros Hc; auto.
  - apply app_eq_nil in Hc.
    constructor; firstorder.
  - inversion Hc; subst; simpl.
    now apply IHl.
Qed.

Lemma in_flat_map_Exists A B : forall (f : A -> list B) x l,
  In x (flat_map f l) <-> Exists (fun y => In x (f y)) l.
Proof.
  intros f x l. 
(* GOAL #228 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #228: 
Tactic call ran for 0.039 secs (0.026u,0.012s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #228: N/A. Non-bool predicate. *)
  rewrite in_flat_map.
  split; apply Exists_exists.
Qed.

Lemma notin_flat_map_Forall A B : forall (f : A -> list B) x l,
  ~ In x (flat_map f l) <-> Forall (fun y => ~ In x (f y)) l.
Proof.
  intros f x l. 
(* GOAL #229 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #229: 
Tactic call ran for 0.003 secs (0.003u,0.s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #229: N/A. Non-bool predicate. *)
rewrite Forall_Exists_neg.
  apply not_iff_compat, in_flat_map_Exists.
Qed.


Section Forall2.

  (** [Forall2]: stating that elements of two lists are pairwise related. *)

  Variables A B : Type.
  Variable R : A -> B -> Prop.

  Inductive Forall2 : list A -> list B -> Prop :=
    | Forall2_nil : Forall2 [] []
    | Forall2_cons : forall x y l l',
      R x y -> Forall2 l l' -> Forall2 (x::l) (y::l').

  #[local]
  Hint Constructors Forall2 : core.

  Theorem Forall2_refl : Forall2 [] [].
  Proof. intros; apply Forall2_nil. Qed.

  Theorem Forall2_app_inv_l : forall l1 l2 l',
    Forall2 (l1 ++ l2) l' ->
    exists l1' l2', Forall2 l1 l1' /\ Forall2 l2 l2' /\ l' = l1' ++ l2'.
  Proof.
    intro l1; induction l1 as [|a l1 IHl1]; intros l2 l' H.
      exists [], l'; auto.
      simpl in H; inversion H as [|? y ? ? ? H4]; subst; clear H.
      apply IHl1 in H4 as (l1' & l2' & Hl1 & Hl2 & ->).
      exists (y::l1'), l2'; simpl; auto.
  Qed.

  Theorem Forall2_app_inv_r : forall l1' l2' l,
    Forall2 l (l1' ++ l2') ->
    exists l1 l2, Forall2 l1 l1' /\ Forall2 l2 l2' /\ l = l1 ++ l2.
  Proof.
    intro l1'; induction l1' as [|a l1' IHl1']; intros l2' l H.
      exists [], l; auto.
      simpl in H; inversion H as [|x ? ? ? ? H4]; subst; clear H.
      apply IHl1' in H4 as (l1 & l2 & Hl1 & Hl2 & ->).
      exists (x::l1), l2; simpl; auto.
  Qed.

  Theorem Forall2_app : forall l1 l2 l1' l2',
    Forall2 l1 l1' -> Forall2 l2 l2' -> Forall2 (l1 ++ l2) (l1' ++ l2').
  Proof.
    intros l1 l2 l1' l2' H H0. induction l1 in l1', H, H0 |- *; inversion H; subst; simpl; auto.
  Qed.
End Forall2.

#[global]
Hint Constructors Forall2 : core.

Section ForallPairs.

  (** [ForallPairs] : specifies that a certain relation should
    always hold when inspecting all possible pairs of elements of a list. *)

  Variable A : Type.
  Variable R : A -> A -> Prop.

  Definition ForallPairs l :=
    forall a b, In a l -> In b l -> R a b.

  (** [ForallOrdPairs] : we still check a relation over all pairs
     of elements of a list, but now the order of elements matters. *)

  Inductive ForallOrdPairs : list A -> Prop :=
    | FOP_nil : ForallOrdPairs nil
    | FOP_cons : forall a l,
      Forall (R a) l -> ForallOrdPairs l -> ForallOrdPairs (a::l).

  #[local]
  Hint Constructors ForallOrdPairs : core.

  Lemma ForallOrdPairs_In : forall l,
    ForallOrdPairs l ->
    forall x y, In x l -> In y l -> x=y \/ R x y \/ R y x.
  Proof.
    induction 1.
    inversion 1.
    simpl; destruct 1; destruct 1; subst; auto.
    right; left. apply -> Forall_forall; eauto.
    right; right. apply -> Forall_forall; eauto.
  Qed.

  (** [ForallPairs] implies [ForallOrdPairs]. The reverse implication is true
    only when [R] is symmetric and reflexive. *)

  Lemma ForallPairs_ForallOrdPairs l: ForallPairs l -> ForallOrdPairs l.
  Proof.
    induction l as [|a l IHl]; auto. intros H.
    constructor.
    apply <- Forall_forall. intros; apply H; simpl; auto.
    apply IHl. red; intros; apply H; simpl; auto.
  Qed.

  Lemma ForallOrdPairs_ForallPairs :
    (forall x, R x x) ->
    (forall x y, R x y -> R y x) ->
    forall l, ForallOrdPairs l -> ForallPairs l.
  Proof.
    intros Refl Sym l Hl x y Hx Hy.
    destruct (ForallOrdPairs_In Hl _ _ Hx Hy); subst; intuition.
  Qed.
End ForallPairs.

Section Repeat.

  Variable A : Type.
  Fixpoint repeat (x : A) (n: nat ) :=
    match n with
      | O => []
      | S k => x::(repeat x k)
    end.

  Theorem repeat_length x n:
    length (repeat x n) = n.
  Proof.
    induction n as [| k Hrec]; simpl.
(* smt. *)
(* GOAL #230 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #230: 
The command has not failed!
Tactic call ran for 0.057 secs (0.u,0.019s) (success)
*)
(* RESULT #230: Smt Success. *)
    rewrite ?Hrec; reflexivity. (* verit. admit. *)
(* GOAL #231 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #231: 
The command has not failed!
Tactic call ran for 0.183 secs (0.023u,0.035s) (success)
*)
(* RESULT #231: Smt Success. *)
    rewrite ?Hrec; reflexivity.
  Qed.

  Theorem repeat_spec n x y:
    In y (repeat x n) -> y=x.
  Proof.
    induction n as [|k Hrec]; simpl; destruct 1; auto.
  Qed.

  Lemma repeat_cons n a :
    a :: repeat a n = repeat a n ++ (a :: nil).
  Proof.
    induction n as [|n IHn]; simpl.
    - reflexivity.
    - f_equal; apply IHn.
  Qed.

  Lemma repeat_app x n m :
    repeat x (n + m) = repeat x n ++ repeat x m.
  Proof.
    induction n as [|n IHn]; simpl; auto. (* verit. admit. admit. *)
(* GOAL #232 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #232: 
The command has not failed!
Tactic call ran for 0.067 secs (0.011u,0.016s) (success)
 *)
(* RESULT #232: Smt Success. *)
    now rewrite IHn.
  Qed.

  Lemma repeat_eq_app x n l1 l2 :
    repeat x n = l1 ++ l2 -> repeat x (length l1) = l1 /\ repeat x (length l2) = l2.
  Proof.
    revert n; induction l1 as [|a l1 IHl1]; simpl; intros n Hr; subst.
    - repeat split. 
(* GOAL #233 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #233: 
Tactic call ran for 0.247 secs (0.006u,0.051s) (failure)
The command has indeed failed with message:
cvc5 returned SAT.
The solver cannot prove the goal, but one of the following hypotheses (printed in Prop, but the corresponding Boolean versions also apply) would make it provable:
((length (A:=A)) (repeat x n)) = n
*) (* assert (((length (A:=A)) (repeat x n)) = n). { 
Search (length (repeat _ _) = _). apply repeat_length. } smt. *)
(* RESULT #233: Success. smt fails on Nat goal. *)
      now rewrite repeat_length.
    - destruct n; inversion Hr as [ [Heq Hr0] ]; subst.
      now apply IHl1 in Hr0 as [-> ->].
  Qed.

  Lemma repeat_eq_cons x y n l :
    repeat x n = y :: l -> x = y /\ repeat x (Nat.pred n) = l.
  Proof.
    intros Hr.
    destruct n; inversion_clear Hr; auto.
  Qed.

  Lemma repeat_eq_elt x y n l1 l2 :
    repeat x n = l1 ++ y :: l2 -> x = y /\ repeat x (length l1) = l1 /\ repeat x (length l2) = l2.
  Proof.
    intros Hr; apply repeat_eq_app in Hr as [Hr1 Hr2]; subst.
    apply repeat_eq_cons in Hr2; intuition.
  Qed.

  Lemma Forall_eq_repeat x l :
    Forall (eq x) l -> l = repeat x (length l).
  Proof.
    induction l as [|a l IHl]; simpl; intros HF; auto.
    inversion_clear HF as [ | ? ? ? HF']; subst. (* verit. *)
(* GOAL #234 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #234: 
The command has not failed!
Discarding the following lemma (unsupported): (Forall (eq a) l : Prop)
[Lemma,SMTCoq plugin]
Tactic call ran for 0.059 secs (0.016u,0.016s) (success)
*)
(* RESULT #234: Smt Success. Drops nat lemma. *)
    now rewrite (IHl HF') at 1.
  Qed.

End Repeat.

Lemma repeat_to_concat A n (a:A) :
  repeat a n = concat (repeat [a] n).
Proof.
  induction n as [|n IHn]; simpl.
  - reflexivity.
  - f_equal; apply IHn.
Qed.


(** Sum of elements of a list of [nat]: [list_sum] *)

Definition list_sum l := fold_right plus 0 l.

Lemma list_sum_app : forall l1 l2,
   list_sum (l1 ++ l2) = list_sum l1 + list_sum l2.
Proof.
intro l1; induction l1 as [|a l1 IHl1]; intros l2; [ reflexivity | ].
simpl. (* GOAL #235 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #235: 
Tactic call ran for 0.081 secs (0.008u,0.024s) (failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName0 Tindex_1)) (= (op_2 (op_1 op_0 SMTCoqRelName0)) (op_3 (op_2 op_0) (op_2 SMTCoqRelName0))) ) ).
*)
(* RESULT #235: N/A. Quantified. Local lemma. *)rewrite IHl1.
apply Nat.add_assoc.
Qed.

(** Max of elements of a list of [nat]: [list_max] *)

Definition list_max l := fold_right max 0 l.

Lemma list_max_app : forall l1 l2,
   list_max (l1 ++ l2) = max (list_max l1) (list_max l2).
Proof.
intro l1; induction l1 as [|a l1 IHl1]; intros l2; [ reflexivity | ].
simpl.
(* GOAL #236 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #236: 
Tactic call ran for 0.068 secs (0.013u,0.008s) (failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName1 Tindex_1)) (= (op_2 (op_1 op_0 SMTCoqRelName1)) (op_3 (op_2 op_0) (op_2 SMTCoqRelName1))) ) ).
*)
(* RESULT #236: N/A. Quantified. Local lemma. *)
rewrite IHl1.
(* GOAL #237 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #237: 
Tactic call ran for 0.094 secs (0.015u,0.016s) (failure)
The command has indeed failed with message:
Solver error: (error The logic was specified as QF_UF, which doesn't include THEORY_QUANTIFIERS, but got a preprocessing-time fact for that theory.
The fact:
(forall ((SMTCoqRelName3 Tindex_1)) (= (op_2 (op_1 op_0 SMTCoqRelName3)) (op_3 (op_2 op_0) (op_2 SMTCoqRelName3))) ) ).
*)
(* RESULT #237: N/A. Quantified. *)
now rewrite Nat.max_assoc.
Qed.

Lemma list_max_le : forall l n,
  list_max l <= n <-> Forall (fun k => k <= n) l.
Proof.
intro l; induction l as [|a l IHl]; simpl; intros n; split; intros H; intuition.
- apply Nat.max_lub_iff in H.
  now constructor; [ | apply IHl ].
- inversion_clear H as [ | ? ? Hle HF ].
  apply IHl in HF; apply Nat.max_lub; assumption.
Qed.

Lemma list_max_lt : forall l n, l <> nil ->
  list_max l < n <-> Forall (fun k => k < n) l.
Proof.
intro l; induction l as [|a l IHl]; simpl; intros n Hnil; split; intros H; intuition.
- destruct l.
  + repeat constructor.
    simpl in H. 
(* GOAL #238 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #238: 
Tactic call ran for 0.049 secs (0.045u,0.004s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #238: N/A. Non-bool predicate. Rewrite in hyp. *)
now rewrite Nat.max_0_r in H.
  + apply Nat.max_lub_lt_iff in H.
    now constructor; [ | apply IHl ].
- destruct l; inversion_clear H as [ | ? ? Hlt HF ].
  + simpl. 
(* GOAL #239 *) (* Fail Timeout 20 (time abduce 1). *)
(* OUTPUT #239: 
Tactic call ran for 0.116 secs (0.095u,0.019s) (failure)
The command has indeed failed with message:
Anomaly
"Uncaught exception Failure("Verit.tactic: can only deal with equality over bool")."
Please report at http://coq.inria.fr/bugs/.
*)
(* RESULT #239: N/A. Non-bool predicate. *)
    now rewrite Nat.max_0_r.
  + apply IHl in HF.
    * now apply Nat.max_lub_lt_iff.
    * intros Heq; inversion Heq.
Qed.


(** * Inversion of predicates over lists based on head symbol *)

Ltac is_list_constr c :=
 match c with
  | nil => idtac
  | (_::_) => idtac
  | _ => fail
 end.

Ltac invlist f :=
 match goal with
  | H:f ?l |- _ => is_list_constr l; inversion_clear H; invlist f
  | H:f _ ?l |- _ => is_list_constr l; inversion_clear H; invlist f
  | H:f _ _ ?l |- _ => is_list_constr l; inversion_clear H; invlist f
  | H:f _ _ _ ?l |- _ => is_list_constr l; inversion_clear H; invlist f
  | H:f _ _ _ _ ?l |- _ => is_list_constr l; inversion_clear H; invlist f
  | _ => idtac
 end.



(** * Exporting hints and tactics *)


Hint Rewrite
  rev_involutive (* rev (rev l) = l *)
  rev_unit (* rev (l ++ a :: nil) = a :: rev l *)
  map_nth (* nth n (map f l) (f d) = f (nth n l d) *)
  map_length (* length (map f l) = length l *)
  seq_length (* length (seq start len) = len *)
  app_length (* length (l ++ l') = length l + length l' *)
  rev_length (* length (rev l) = length l *)
  app_nil_r (* l ++ nil = l *)
  : list.

Ltac simpl_list := autorewrite with list.
Ltac ssimpl_list := autorewrite with list using simpl.

(* begin hide *)
(* Compatibility notations after the migration of [list] to [Datatypes] *)
Notation list := list (only parsing).
Notation list_rect := list_rect (only parsing).
Notation list_rec := list_rec (only parsing).
Notation list_ind := list_ind (only parsing).
Notation nil := nil (only parsing).
Notation cons := cons (only parsing).
Notation length := length (only parsing).
Notation app := app (only parsing).
(* Compatibility Names *)
Notation tail := tl (only parsing).
Notation head := hd_error (only parsing).
Notation head_nil := hd_error_nil (only parsing).
Notation head_cons := hd_error_cons (only parsing).
Notation ass_app := app_assoc (only parsing).
Notation app_ass := app_assoc_reverse (only parsing).
Notation In_split := in_split (only parsing).
Notation In_rev := in_rev (only parsing).
Notation In_dec := in_dec (only parsing).
Notation distr_rev := rev_app_distr (only parsing).
Notation rev_acc := rev_append (only parsing).
Notation rev_acc_rev := rev_append_rev (only parsing).
Notation AllS := Forall (only parsing). (* was formerly in TheoryList *)

#[global]
Hint Resolve app_nil_end : datatypes.
(* end hide *)


(* Unset Universe Polymorphism. *)
