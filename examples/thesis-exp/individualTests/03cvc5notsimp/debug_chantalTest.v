
(** studying chantalTest **)
Add Rec LoadPath "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/src" as SMTCoq.
From SMTCoq Require Import SMTCoq.
Require Import Bool PArray Int63 List ZArith.
Local Open Scope int63_scope.
Open Scope Z_scope.
Set Printing Depth 250.
Module chantalTest.
Section chantalTest.
Parse_certif_verit t_i t_func t_atom t_form root used_roots trace "chantalTest.smt2" "chantalTest.pf".
Compute @Euf_Checker.checker t_i t_func t_atom t_form root used_roots trace.
Compute (Form.check_form t_form && Atom.check_atom t_atom && Atom.wt t_i t_func t_atom).
Definition nclauses := Eval compute in let (nclauses, _, _) := trace in nclauses.
Print trace.
Definition s0 := Eval compute in (add_roots (S.make nclauses) root used_roots).
 Definition s1 := Eval compute in step_checker s0 (BuildDef2 (t_i:=t_i) t_func  t_atom  t_form  2 7).
Print s1.
(*s1 =({|Map.this := 0[4]( 1[5]( 2[4 , 5 , 7]));Map.is_bst := 2 [4 , 5 , 7]( 1 [5]( 0 [4]( [list int))))|}, 0, 5]: Map.bst * list int * in*)
 Definition s2 := Eval compute in step_checker s1 (BuildDef (t_i:=t_i) t_func  t_atom  t_form  3 6).
Print s2.
(*s2 =({|Map.this :=( 0[4] ) 1[5]( 2[4 , 5 , 7]( 3[5 , 6] ));Map.is_bst := 3 [5 , 6]( 2 [4 , 5 , 7]( 1 [5]( 0 [4]( [list int)))))|}, 0, 5]: Map.bst * list int * in*)
 Definition s3 := Eval compute in step_checker s2 (BuildDef2 (t_i:=t_i) t_func  t_atom  t_form  4 6).
Print s3.
(*s3 =({|Map.this :=( 0[4] ) 1[5]( 2[4 , 5 , 7]( 3[5 , 6]( 4[4 , 6] )))4;Map.is_bst := 4 [4 , 6]( 3 [5 , 6]( 2[4 , 5 , 7]( 1 [5]( 0 [4]( [list int))))))|}, 0, 5]: Map.bst * list int * in*)
 Definition s4 := Eval compute in step_checker s3 (Res (t_i:=t_i) t_func  t_atom  t_form  4((make 2 0%int63 .[ 0 <- 3%int63]) .[ 1 <- 4%int63])%array).
Print s4.
(*s4 =({|Map.this :=( 0[4] ) 1[5]( 2[4 , 5 , 7]( 3[5 , 6]( 4[6] )));Map.is_bst := 4 [6]( 4 [4 , 6]( 3 [5 , 6]( 2[4 , 5 , 7]( 1 [5]( 0[4] ( [list int)))))))|}, 0, 5]: Map.bst * list int * in*)
 Definition s5 := Eval compute in step_checker s4 (Res (t_i:=t_i) t_func  t_atom  t_form  0(((make 3 0%int63 .[ 0 <- 2%int63]) .[ 1 <- 4%int63]).[ 2 <- 0%int63])%array).
Print s5.
(*s5 =({|Map.this :=( 0[4 , 0] ) 1[5]( 2[4 , 5 , 7]( 3[5 , 6]( 4[6] )));Map.is_bst := 0 [4 , 0]( 4 [6]( 4 [4 , 6]( 3 [5 , 6]( 2[4 , 5 , 7]( 1[5]( 0[4]( [list int))))))))|}, 0, 5]: Map.bst * list int * in*)
(* ====> ":: 0%int63 " in output found, break *)
Definition confl := Eval compute in let (_, _, confl) := trace in confl.
Compute (C.is_false (S.get s5 confl)).