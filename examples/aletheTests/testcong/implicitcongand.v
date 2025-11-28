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
   
   (*Local Open Scope int63_scope.*)
   Local Open Scope int31_scope.
   Local Open Scope array_scope.
   Local Open Scope int63_scope.
   
   Section CongP.
     Verit_Checker "implicitcongand.smt2" "implicitcongand.pf".
   End CongP.