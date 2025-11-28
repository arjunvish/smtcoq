(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2021                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

Require Import SMTCoq.SMTCoq.
Require Import Bool.

Require Import ZArith.
Require Import Int31.

Import BVList.BITVECTOR_LIST.
Local Open Scope bv_scope.

Import FArray.
Local Open Scope farray_scope.

(* Examples that check ZChaff certificates *)

(*Local Open Scope int63_scope.*)
Local Open Scope int31_scope.
Local Open Scope array_scope.
Local Open Scope int63_scope.

Section AndSimp.
  Verit_Checker "andsimp.smt2" "andsimp.pf".
End AndSimp.

Section NotSimp1.
  Verit_Checker "notsimp1.smt2" "notsimp1.pf".
End NotSimp1.

Section NotSimp2.
  Verit_Checker "notsimp2.smt2" "notsimp2.pf".
End NotSimp2.