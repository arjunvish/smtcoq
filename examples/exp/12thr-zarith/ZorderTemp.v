(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Binary Integers : results about order predicates *)
(** Initial author : Pierre Crégut (CNET, Lannion, France) *)

(** THIS FILE IS DEPRECATED.
    It is now almost entirely made of compatibility formulations
    for results already present in BinInt.Z. *)

Require Import BinPos BinInt Decidable Zcompare.
Require Import Arith_base. (* Useless now, for compatibility only *)

Local Open Scope Z_scope.

Add Rec LoadPath "/home/arjun/Desktop/smtcoq/abduction-arjunvish-smtcoq/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.

(*********************************************************)
(** Properties of the order relations on binary integers *)

(** * Trichotomy *)

Theorem Ztrichotomy_inf n m : {n < m} + {n = m} + {n > m}.
Proof.
  unfold ">", "<". generalize (Z.compare_eq n m).
  destruct (n ?= m); [ left; right | left; left | right]; auto.
Defined.

Theorem Ztrichotomy n m : n < m \/ n = m \/ n > m.
Proof.
  smt.
Qed.

(**********************************************************************)
(** * Decidability of equality and order on Z *)

Notation dec_eq := Z.eq_decidable (only parsing).
Notation dec_Zle := Z.le_decidable (only parsing).
Notation dec_Zlt := Z.lt_decidable (only parsing).

Theorem dec_Zne n m : decidable (Zne n m).
Proof.
  destruct (Z.eq_decidable n m); [right|left]; subst; auto.
Qed.

Theorem dec_Zgt n m : decidable (n > m).
Proof.
  destruct (Z.lt_decidable m n); [left|right]; Z.swap_greater; auto.
Qed.

Theorem dec_Zge n m : decidable (n >= m).
Proof.
  destruct (Z.le_decidable m n); [left|right]; Z.swap_greater; auto.
Qed.

Theorem not_Zeq n m : n <> m -> n < m \/ m < n.
Proof. 
  smt.
Qed.

Register dec_Zne as plugins.omega.dec_Zne.
Register dec_Zgt as plugins.omega.dec_Zgt.
Register dec_Zge as plugins.omega.dec_Zge.
Register not_Zeq as plugins.omega.not_Zeq.

(** * Relating strict and large orders *)

Notation Zgt_iff_lt := Z.gt_lt_iff (only parsing).
Notation Zge_iff_le := Z.ge_le_iff (only parsing).

Lemma Zle_not_lt n m : n <= m -> ~ m < n.
Proof. smt. Qed.

Lemma Zlt_not_le n m : n < m -> ~ m <= n.
Proof. smt. Qed.

Lemma Zle_not_gt n m : n <= m -> ~ n > m.
Proof. smt. Qed.

Lemma Zgt_not_le n m : n > m -> ~ n <= m.
Proof. smt. Qed.

Lemma Znot_ge_lt n m : ~ n >= m -> n < m.
Proof. smt. Qed.

Lemma Znot_lt_ge n m : ~ n < m -> n >= m.
Proof. smt. Qed.

Lemma Znot_gt_le n m: ~ n > m -> n <= m.
Proof. smt. Qed.

Lemma Znot_le_gt n m : ~ n <= m -> n > m.
Proof. smt. Qed.

Lemma not_Zne n m : ~ Zne n m -> n = m.
Proof.
  intros H.
  destruct (Z.eq_decidable n m); [assumption|now elim H].
Qed.

Register Znot_le_gt as plugins.omega.Znot_le_gt.
Register Znot_lt_ge as plugins.omega.Znot_lt_ge.
Register Znot_ge_lt as plugins.omega.Znot_ge_lt.
Register Znot_gt_le as plugins.omega.Znot_gt_le.
Register not_Zne as plugins.omega.not_Zne.

(** * Equivalence and order properties *)

(** Reflexivity *)

Notation Zeq_le := Z.eq_le_incl (only parsing).

#[global]
Hint Resolve Z.le_refl: zarith.

(** Antisymmetry *)

Notation Zle_antisym := Z.le_antisymm (only parsing).

(** Asymmetry *)

Notation Zlt_asym := Z.lt_asymm (only parsing).

Lemma Zgt_asym n m : n > m -> ~ m > n.
Proof. smt. Qed.

(** Irreflexivity *)

Notation Zlt_not_eq := Z.lt_neq (only parsing).

Lemma Zgt_irrefl n : ~ n > n.
Proof. smt. Qed.

(** Large = strict or equal *)

Notation Zlt_le_weak := Z.lt_le_incl (only parsing).
Notation Zle_lt_or_eq_iff := Z.lt_eq_cases (only parsing).

Lemma Zle_lt_or_eq n m : n <= m -> n < m \/ n = m.
Proof. smt. Qed.

(** Dichotomy *)

Notation Zle_or_lt := Z.le_gt_cases (only parsing).

(** Transitivity of strict orders *)

Lemma Zgt_trans n m p : n > m -> m > p -> n > p.
Proof. smt. Qed.

(** Mixed transitivity *)

Lemma Zle_gt_trans n m p : m <= n -> m > p -> n > p.
Proof. smt. Qed.

Lemma Zgt_le_trans n m p : n > m -> p <= m -> n > p.
Proof. smt. Qed.

(** Transitivity of large orders *)

Lemma Zge_trans n m p : n >= m -> m >= p -> n >= p.
Proof. smt. Qed.

#[global]
Hint Resolve Z.le_trans: zarith.

(** * Compatibility of order and operations on Z *)

(** ** Successor *)

(** Compatibility of successor wrt to order *)

Lemma Zsucc_le_compat n m : m <= n -> Z.succ m <= Z.succ n.
Proof. 
 (* cvc5_abduct_no_quant 4.
    n = m
    n <= m
    (Z.succ n) = (Z.succ m)
    (Z.succ m) <= (Z.succ n) *)
  apply Z.succ_le_mono.
Qed.

(* PASS *)
Lemma Zsucc_lt_compat n m : n < m -> Z.succ n < Z.succ m.
Proof. (* unfold Z.succ. smt. *)
 (* cvc5_abduct_no_quant 3. (sygus-enum=default)
    (Z.succ n) + 1 = (Z.succ m)
    (Z.succ n) + 1 <= (Z.succ m)
    (Z.succ m) + n = (Z.succ n) + m *)
 (* cvc5_abduct_no_quant 1. (sygus-enum=fast)
    (not (Z.succ m) <= (Z.succ n)) *)
  assert ((Z.succ m) + n = (Z.succ n) + m). { unfold Z.succ. smt. }
  smt.
Qed.

Lemma Zsucc_gt_compat n m : m > n -> Z.succ m > Z.succ n.
Proof.
 (* cvc5_abduct_no_quant 2.
    (not (Z.succ m) <= (Z.succ n)) *)
  Z.swap_greater. apply Z.succ_lt_mono.
Qed.

#[global]
Hint Resolve Zsucc_le_compat: zarith.

(** Simplification of successor wrt to order *)

Lemma Zsucc_gt_reg n m : Z.succ m > Z.succ n -> m > n.
Proof.
 (* cvc5_abduct_no_quant 1.
    n <= m *)
  Z.swap_greater. apply Z.succ_lt_mono.
Qed.

Lemma Zsucc_le_reg n m : Z.succ m <= Z.succ n -> m <= n.
Proof. 
 (* cvc5_abduct_no_quant 2.
    m = n
    m <= n *)
  apply Z.succ_le_mono.
Qed.

Lemma Zsucc_lt_reg n m : Z.succ n < Z.succ m -> n < m.
Proof. 
 (* cvc5_abduct_no_quant 1. 
    n <= m *)
  apply Z.succ_lt_mono.
Qed.

(** Special base instances of order *)

Notation Zlt_succ := Z.lt_succ_diag_r (only parsing).
Notation Zlt_pred := Z.lt_pred_l (only parsing).

Lemma Zgt_succ n : Z.succ n > n.
Proof. 
 (* cvc5_abduct_no_quant 1.
    (not (Z.succ n) <= n) *)
  Z.swap_greater. apply Z.lt_succ_diag_r.
Qed.

Lemma Znot_le_succ n : ~ Z.succ n <= n.
Proof.
 (* cvc5_abduct_no_quant 1.
    (not (Z.succ n) <= n) *)
  apply Z.lt_nge, Z.lt_succ_diag_r.
Qed.

(** Relating strict and large order using successor or predecessor *)

Lemma Zgt_le_succ n m : m > n -> Z.succ n <= m.
Proof.
 (* cvc5_abduct_no_quant 1.
    n = (Z.succ n) *)
  Z.swap_greater. apply Z.le_succ_l.
Qed.

(* PASS *)
Lemma Zle_gt_succ n m : n <= m -> Z.succ m > n.
Proof. 
 (* cvc5_abduct 3.
    (Z.succ m) = 1 + m
    (Z.succ m) = n + 1
    n + 1 <= (Z.succ m) *)
  assert (Z.succ m = 1 + m). { unfold Z.succ. now rewrite Z.add_comm. }
  smt.
Qed.

(* PASS *)
Lemma Zle_lt_succ n m : n <= m -> n < Z.succ m.
Proof.
 (* cvc5_abduct 3.
    (Z.succ m) = 1 + m
    (Z.succ m) = n + 1
    n + 1 <= (Z.succ m) *)
  assert (Z.succ m = 1 + m). { unfold Z.succ. now rewrite Z.add_comm. }
  smt.
Qed.

(* PASS *)
Lemma Zlt_le_succ n m : n < m -> Z.succ n <= m.
Proof.
 (* cvc5_abduct 3.
    (Z.succ n) <= n
    (Z.succ n) <= m
    (Z.succ n) = n + 1 *)
  assert (Z.succ n = 1 + n). { unfold Z.succ. now rewrite Z.add_comm. }
  smt.
Qed.

(* PASS *)
Lemma Zgt_succ_le n m : Z.succ m > n -> n <= m.
Proof.
 (* cvc5_abduct 3.
    n <= m
    (Z.succ m) <= m
    (Z.succ m) = m + 1 *)
  assert (Z.succ m = 1 + m). { unfold Z.succ. now rewrite Z.add_comm. }
  smt.
Qed.

Lemma Zlt_succ_le n m : n < Z.succ m -> n <= m.
Proof.
  apply Z.lt_succ_r.
Qed.

(* Pass *)
Lemma Zle_succ_gt n m : Z.succ n <= m -> m > n.
Proof.
 (* cvc5_abduct 3.
    n + 1 <= m
    n + 1 = (Z.succ n)
    n + 1 <= (Z.succ n) *)
  assert (n + 1 = (Z.succ n)). { now unfold Z.succ. }
  smt.
Qed.

(** Weakening order *)

Notation Zle_succ := Z.le_succ_diag_r (only parsing).
Notation Zle_pred := Z.le_pred_l (only parsing).
Notation Zlt_lt_succ := Z.lt_lt_succ_r (only parsing).
Notation Zle_le_succ := Z.le_le_succ_r (only parsing).
(* Pass *)
Lemma Zle_succ_le n m : Z.succ n <= m -> n <= m.
Proof.
 (* cvc5_abduct 3.
    n <= m
    n <= (Z.succ n)
    1 <= (Z.succ n) && m + n = 1 *)
  assert (n <= (Z.succ n)). { unfold Z.succ. smt. }
  smt.
Qed.

#[global]
Hint Resolve Z.le_succ_diag_r: zarith.
#[global]
Hint Resolve Z.le_le_succ_r: zarith.

(** Relating order wrt successor and order wrt predecessor *)
(* PASS *)
Lemma Zgt_succ_pred n m : m > Z.succ n -> Z.pred m > n.
Proof.
 (* cvc5_abduct 2.
    (Z.pred m) = n + 1
    n + 1 <= (Z.pred m) *)
  intros. assert (n + 1 <= (Z.pred m)). 
  { unfold Z.pred. unfold Z.succ in H. smt. }
  smt.
Qed.

Lemma Zlt_succ_pred n m : Z.succ n < m -> n < Z.pred m.
Proof.
 (* cvc5_abduct 2.
    (Z.pred m) = 1 + n
    1 + n <= (Z.pred m) *)
  intros. assert (1 + n <= (Z.pred m)). 
  { unfold Z.pred. unfold Z.succ in H. smt. }
  smt.
Qed.

(** Relating strict order and large order on positive *)
(* PASS *)
Lemma Zlt_0_le_0_pred n : 0 < n -> 0 <= Z.pred n.
Proof.
 (* cvc5_abduct 4.
    1 <= (Z.pred n)
    n <= (Z.pred n)
    0 <= (Z.pred n)
    (Z.pred n) + 1 = n *)
  intros. assert ((Z.pred n) + 1 = n). { unfold Z.pred. smt. }
  smt.
Qed.

(* PASS *)
Lemma Zgt_0_le_0_pred n : n > 0 -> 0 <= Z.pred n.
Proof.
 (* cvc5_abduct 3.
    1 <= (Z.pred n)
    n <= (Z.pred n)
    0 <= (Z.pred n) *)
  intros. assert (0 <= (Z.pred n)). { unfold Z.pred. smt. }
  smt.
Qed.

(** Special cases of ordered integers *)
(* Arjun: we convert positive to Z *)
Lemma Zle_neg_pos : forall p q:positive, Zneg p <= Zpos q.
Proof.
  exact Pos2Z.neg_le_pos.
Qed.

Lemma Zgt_pos_0 : forall p:positive, Zpos p > 0.
Proof.
  easy.
Qed.

(* weaker but useful (in [Z.pow] for instance) *)
Lemma Zle_0_pos : forall p:positive, 0 <= Zpos p.
Proof.
  exact Pos2Z.pos_is_nonneg.
Qed.

Lemma Zlt_neg_0 : forall p:positive, Zneg p < 0.
Proof.
  exact Pos2Z.neg_is_neg.
Qed.

Lemma Zle_0_nat : forall n:nat, 0 <= Z.of_nat n.
Proof. 
 (* cvc5_abduct 3.
    (Z.of_nat n) = 1
    (Z.of_nat n) = 0
    0 <= (Z.of_nat n) *)
  intros n; induction n; simpl; intros. apply Z.le_refl. easy.
Qed.

#[global]
Hint Immediate Z.eq_le_incl: zarith.

(** Derived lemma *)

(* PASS *)
Lemma Zgt_succ_gt_or_eq n m : Z.succ n > m -> n > m \/ m = n.
Proof. 
 (* cvc5_abduct 3.
    m <= n
    (Z.succ n) <= n
    (Z.succ n) = n + 1 *)
    intros. assert ((Z.succ n) = n + 1). { unfold Z.succ. smt. }
    smt.
Qed.

(** ** Addition *)
(** Compatibility of addition wrt to order *)

Notation Zplus_lt_le_compat := Z.add_lt_le_mono (only parsing).
Notation Zplus_le_lt_compat := Z.add_le_lt_mono (only parsing).
Notation Zplus_le_compat := Z.add_le_mono (only parsing).
Notation Zplus_lt_compat := Z.add_lt_mono (only parsing).

Lemma Zplus_gt_compat_l n m p : n > m -> p + n > p + m.
Proof.
  smt.
Qed.

Lemma Zplus_gt_compat_r n m p : n > m -> n + p > m + p.
Proof.
  smt.
Qed.

Lemma Zplus_le_compat_l n m p : n <= m -> p + n <= p + m.
Proof.
  smt.
Qed.

Lemma Zplus_le_compat_r n m p : n <= m -> n + p <= m + p.
Proof.
  smt.
Qed.

Lemma Zplus_lt_compat_l n m p : n < m -> p + n < p + m.
Proof.
  smt.
Qed.

Lemma Zplus_lt_compat_r n m p : n < m -> n + p < m + p.
Proof.
  smt.
Qed.

(** Compatibility of addition wrt to being positive *)

Notation Zplus_le_0_compat := Z.add_nonneg_nonneg (only parsing).

(** Simplification of addition wrt to order *)

Lemma Zplus_le_reg_l n m p : p + n <= p + m -> n <= m.
Proof.
 smt.
Qed.

Lemma Zplus_le_reg_r n m p : n + p <= m + p -> n <= m.
Proof.
 smt.
Qed.

Lemma Zplus_lt_reg_l n m p : p + n < p + m -> n < m.
Proof.
 smt.
Qed.

Lemma Zplus_lt_reg_r n m p : n + p < m + p -> n < m.
Proof.
 smt.
Qed.

Lemma Zplus_gt_reg_l n m p : p + n > p + m -> n > m.
Proof.
 smt.
Qed.

Lemma Zplus_gt_reg_r n m p : n + p > m + p -> n > m.
Proof.
 smt.
Qed.

(** ** Multiplication *)
(** Compatibility of multiplication by a positive wrt to order *)

Lemma Zmult_le_compat_r n m p : n <= m -> 0 <= p -> n * p <= m * p.
Proof.
 intros. now apply Z.mul_le_mono_nonneg_r.
Qed.

Lemma Zmult_le_compat_l n m p : n <= m -> 0 <= p -> p * n <= p * m.
Proof.
 intros. now apply Z.mul_le_mono_nonneg_l.
Qed.

Lemma Zmult_lt_compat_r n m p : 0 < p -> n < m -> n * p < m * p.
Proof.
 apply Z.mul_lt_mono_pos_r.
Qed.

Lemma Zmult_gt_compat_r n m p : p > 0 -> n > m -> n * p > m * p.
Proof.
 Z.swap_greater. apply Z.mul_lt_mono_pos_r.
Qed.

Lemma Zmult_gt_0_lt_compat_r n m p : p > 0 -> n < m -> n * p < m * p.
Proof.
 Z.swap_greater. apply Z.mul_lt_mono_pos_r.
Qed.

Lemma Zmult_gt_0_le_compat_r n m p : p > 0 -> n <= m -> n * p <= m * p.
Proof.
 Z.swap_greater. apply Z.mul_le_mono_pos_r.
Qed.

Lemma Zmult_lt_0_le_compat_r n m p : 0 < p -> n <= m -> n * p <= m * p.
Proof.
 apply Z.mul_le_mono_pos_r.
Qed.

Lemma Zmult_gt_0_lt_compat_l n m p : p > 0 -> n < m -> p * n < p * m.
Proof.
 Z.swap_greater. apply Z.mul_lt_mono_pos_l.
Qed.

Lemma Zmult_lt_compat_l n m p : 0 < p -> n < m -> p * n < p * m.
Proof.
 apply Z.mul_lt_mono_pos_l.
Qed.

Lemma Zmult_gt_compat_l n m p : p > 0 -> n > m -> p * n > p * m.
Proof.
 Z.swap_greater. apply Z.mul_lt_mono_pos_l.
Qed.

Lemma Zmult_ge_compat_r n m p : n >= m -> p >= 0 -> n * p >= m * p.
Proof.
 Z.swap_greater. intros. now apply Z.mul_le_mono_nonneg_r.
Qed.

Lemma Zmult_ge_compat_l n m p : n >= m -> p >= 0 -> p * n >= p * m.
Proof.
 Z.swap_greater. intros. now apply Z.mul_le_mono_nonneg_l.
Qed.

Lemma Zmult_ge_compat n m p q :
  n >= p -> m >= q -> p >= 0 -> q >= 0 -> n * m >= p * q.
Proof.
 Z.swap_greater. intros. now apply Z.mul_le_mono_nonneg.
Qed.

Lemma Zmult_le_compat n m p q :
  n <= p -> m <= q -> 0 <= n -> 0 <= m -> n * m <= p * q.
Proof.
 intros. now apply Z.mul_le_mono_nonneg.
Qed.

(** Simplification of multiplication by a positive wrt to being positive *)

Lemma Zmult_gt_0_lt_reg_r n m p : p > 0 -> n * p < m * p -> n < m.
Proof.
 Z.swap_greater. apply Z.mul_lt_mono_pos_r.
Qed.

Lemma Zmult_lt_reg_r n m p : 0 < p -> n * p < m * p -> n < m.
Proof.
 apply Z.mul_lt_mono_pos_r.
Qed.

Lemma Zmult_le_reg_r n m p : p > 0 -> n * p <= m * p -> n <= m.
Proof.
 Z.swap_greater. apply Z.mul_le_mono_pos_r.
Qed.

Lemma Zmult_lt_0_le_reg_r n m p : 0 < p -> n * p <= m * p -> n <= m.
Proof.
 apply Z.mul_le_mono_pos_r.
Qed.

Lemma Zmult_ge_reg_r n m p : p > 0 -> n * p >= m * p -> n >= m.
Proof.
 Z.swap_greater. apply Z.mul_le_mono_pos_r.
Qed.

Lemma Zmult_gt_reg_r n m p : p > 0 -> n * p > m * p -> n > m.
Proof.
 Z.swap_greater. apply Z.mul_lt_mono_pos_r.
Qed.

Lemma Zmult_lt_compat n m p q :
  0 <= n < p -> 0 <= m < q -> n * m < p * q.
Proof.
 intros (Hn,Hnp) (Hm,Hmq). now apply Z.mul_lt_mono_nonneg.
Qed.

Lemma Zmult_lt_compat2 n m p q :
  0 < n <= p -> 0 < m < q -> n * m < p * q.
Proof.
  intros (Hn, Hnp) (Hm,Hmq).
  apply Z.le_lt_trans with (p * m).
   apply Z.mul_le_mono_pos_r; trivial.
   apply Z.mul_lt_mono_pos_l; Z.order.
Qed.

(** Compatibility of multiplication by a positive wrt to being positive *)

Notation Zmult_le_0_compat := Z.mul_nonneg_nonneg (only parsing).
Notation Zmult_lt_0_compat := Z.mul_pos_pos (only parsing).
Notation Zmult_lt_O_compat := Z.mul_pos_pos (only parsing).

Lemma Zmult_gt_0_compat n m : n > 0 -> m > 0 -> n * m > 0.
Proof.
 Z.swap_greater. apply Z.mul_pos_pos.
Qed.

(* To remove someday ... *)

Lemma Zmult_gt_0_le_0_compat n m : n > 0 -> 0 <= m -> 0 <= m * n.
Proof.
 Z.swap_greater. intros. apply Z.mul_nonneg_nonneg. trivial.
  now apply Z.lt_le_incl.
Qed.

(** Simplification of multiplication by a positive wrt to being positive *)

Lemma Zmult_le_0_reg_r n m : n > 0 -> 0 <= m * n -> 0 <= m.
Proof.
 Z.swap_greater. apply Z.mul_nonneg_cancel_r.
Qed.

Lemma Zmult_lt_0_reg_r n m : 0 < n -> 0 < m * n -> 0 < m.
Proof.
 apply Z.mul_pos_cancel_r.
Qed.

Lemma Zmult_gt_0_lt_0_reg_r n m : n > 0 -> 0 < m * n -> 0 < m.
Proof.
 Z.swap_greater. apply Z.mul_pos_cancel_r.
Qed.

Lemma Zmult_gt_0_reg_l n m : n > 0 -> n * m > 0 -> m > 0.
Proof.
 Z.swap_greater. apply Z.mul_pos_cancel_l.
Qed.

(** ** Square *)
(** Simplification of square wrt order *)

Lemma Zlt_square_simpl n m : 0 <= n -> m * m < n * n -> m < n.
Proof.
 apply Z.square_lt_simpl_nonneg.
Qed.

Lemma Zgt_square_simpl n m : n >= 0 -> n * n > m * m -> n > m.
Proof.
 Z.swap_greater. apply Z.square_lt_simpl_nonneg.
Qed.

(** * Equivalence between inequalities *)

Notation Zle_plus_swap := Z.le_add_le_sub_r (only parsing).
Notation Zlt_plus_swap := Z.lt_add_lt_sub_r (only parsing).
Notation Zlt_minus_simpl_swap := Z.lt_sub_pos (only parsing).

Lemma Zeq_plus_swap n m p : n + p = m <-> n = m - p.
Proof. 
  smt.
Qed.

Lemma Zlt_0_minus_lt n m : 0 < n - m -> m < n.
Proof.
 smt.
Qed.

Lemma Zle_0_minus_le n m : 0 <= n - m -> m <= n.
Proof.
 smt.
Qed.

Lemma Zle_minus_le_0 n m : m <= n -> 0 <= n - m.
Proof.
 smt.
Qed.

(** For compatibility *)
Notation Zlt_O_minus_lt := Zlt_0_minus_lt (only parsing).
