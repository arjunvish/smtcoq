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
   
Section Test.
  Verit_Checker "testtaut.smt2" "testtaut.pf".
End Test.