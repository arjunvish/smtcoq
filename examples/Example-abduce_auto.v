(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2022                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


(* [Require Import SMTCoq.SMTCoq.] loads the SMTCoq library.
   If you are using native-coq instead of Coq 8.11, replace it with:
     Require Import SMTCoq.
   *)
Require Import SMTCoq.SMTCoq.
Require Import Bool.

Require Import ZArith.

Local Open Scope Z_scope.
(* Examples of the abduce tactic (requires cvc5 in your PATH environment
   variable) *)

(* Consider a previous example with one of the implicative
   hypotheses commented out *)
Goal forall
    (x y: Z)
    (f: Z -> Z),
    (* x = y + 1 -> *) f y = f (x - 1).
Proof.
  Fail smt. Fail abduce_auto 1.
(* The command has indeed failed with message:
   cvc5 returned SAT.
   The solver cannot prove the goal, but one of the following hypotheses would make it provable:
   x - 1 = y *)
Abort.

(* SMTCoq currently doesn't support non-linear arithmetic *)
Goal forall (x y : Z),
  x = y + 1 -> x * x = (y + 1) * x.
Proof. Fail smt. Abort.

(* However, it can try to prove these goals by considering
   multiplication to be an uninterpreted function *)
Definition mul' := Z.mul.
Notation "x *' y" := (mul' x y) (at level 1).

Goal forall (x y : Z),
  x = y + 1 -> x *' x = (y + 1) *' x.
Proof. smt. Qed.

(* This is not always possible because multiplication is
   underspecified to the external solver *)
Goal forall (x y z: Z),
    x = y + 1 -> y *' z = z *' (x - 1).
Proof. Fail smt.
(* Now, we can ask for abducts that would help close the
   specification gap *)
   Fail abduce 3.
(* The command has indeed failed with message:
   cvc5 returned SAT.
   The solver cannot prove the goal, but one of the following hypotheses would make it provable:
   z = y
   x - 1 = z
   (mul' y z) = (mul' z y) *)
   intros. assert ((mul' y z) = (mul' z y)).
   { apply Z.mul_comm. } smt.
Qed.