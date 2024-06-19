
(** studying min **)
Add Rec LoadPath "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/src" as SMTCoq.
From SMTCoq Require Import SMTCoq.
Require Import Bool PArray Int63 List ZArith.
Local Open Scope int63_scope.
Open Scope Z_scope.
Set Printing Depth 250.
Module min.
Section min.
Parse_certif_verit t_i t_func t_atom t_form root used_roots trace "min.smt2" "min.pf".
Compute @Euf_Checker.checker t_i t_func t_atom t_form root used_roots trace.
Compute (Form.check_form t_form && Atom.check_atom t_atom && Atom.wt t_i t_func t_atom).
Definition nclauses := Eval compute in let (nclauses, _, _) := trace in nclauses.
Print trace.
Definition s0 := Eval compute in (add_roots (S.make nclauses) root used_roots).
 Definition s1 := Eval compute in step_checker s0 (BuildDef (t_i:=t_i) t_func  t_atom  t_form  1 8).
Print s1.
(*s1 =({|Map.this := 0[7]( 1[5 , 8] );Map.is_bst := 1 [5 , 8]( 0 [7]( [list int)))|}, 0, 4]: Map.bst * list int * in*)
 Definition s2 := Eval compute in step_checker s1 (BuildDef2 (t_i:=t_i) t_func  t_atom  t_form  2 8).
Print s2.
(*s2 =({|Map.this := 0[7]( 1[5 , 8]( 2[4 , 8] ));Map.is_bst := 2 [4 , 8]( 1 [5 , 8]( 0 [7]( [list int))))|}, 0, 4]: Map.bst * list int * in*)
 Definition s3 := Eval compute in step_checker s2 (Res (t_i:=t_i) t_func  t_atom  t_form  2((make 2 0%int63 .[ 0 <- 1%int63]) .[ 1 <- 2%int63])%array).
Print s3.
(*s3 =({|Map.this := 0[7]( 1[5 , 8]( 2[8] ));Map.is_bst := 2 [8]( 2 [4 , 8]( 1 [5 , 8]( 0 [7]( [list int)))))|}, 0, 4]: Map.bst * list int * in*)
 Definition s4 := Eval compute in step_checker s3 (BuildDef (t_i:=t_i) t_func  t_atom  t_form  1 6).
Print s4.
(*s4 =({|Map.this := 0[7]( 1[4 , 6]( 2[8] ));Map.is_bst := 1 [4 , 6]( 2 [8]( 2 [4 , 8]( 1 [5 , 8]( 0 [7]( [list int))))))|}, 0, 4]: Map.bst * list int * in*)
 Definition s5 := Eval compute in step_checker s4 (Weaken (t_i:=t_i) t_func  t_atom  t_form  1 1(9%int63 :: 6%int63 :: 4%int63 :: 4%int63 :: nil)).
Print s5.
(*s5 =({|Map.this := 0[7]( 1[4 , 4 , 6 , 9]( 2[8] ));Map.is_bst := 1[4 , 4 , 6 , 9]( 1 [4 , 6]( 2 [8]( 2 [4 , 8]( 1 [5 , 8]( 0[7] ( [list int)))))))|}, 0, 4]: Map.bst * list int * in*)
 Definition s6 := Eval compute in step_checker s5 (Res (t_i:=t_i) t_func  t_atom  t_form  1((make 2 0%int63 .[ 0 <- 1%int63]) .[ 1 <- 2%int63])%array).
Print s6.
(*s6 =({|Map.this := 0[7]( 1[4 , 4 , 6]( 2[8] ));Map.is_bst := 1 [4 , 4 , 6]( 1[4 , 4 , 6 , 9]( 1 [4 , 6]( 2 [8]( 2 [4 , 8]( 1[5 , 8]( 0[7]( [list int))))))))|}, 0, 4]: Map.bst * list int * in*)
 Definition s7 := Eval compute in step_checker s6 (BuildDef2 (t_i:=t_i) t_func  t_atom  t_form  3 6).
Print s7.
(*s7 =({|Map.this :=( 0[7] ) 1[4 , 4 , 6]( 2[8]( 3[5 , 6] ));Map.is_bst := 3 [5 , 6]( 1 [4 , 4 , 6]( 1[4 , 4 , 6 , 9]( 1 [4 , 6]( 2 [8]( 2[4 , 8]( 1[5 , 8]( 0[7]( [list int)))))))))|}, 0, 4]: Map.bst * list int * in*)
 Definition s8 := Eval compute in step_checker s7 (Weaken (t_i:=t_i) t_func  t_atom  t_form  3 3(9%int63 :: 6%int63 :: 5%int63 :: 5%int63 :: nil)).
Print s8.
(*s8 =({|Map.this :=( 0[7] ) 1[4 , 4 , 6]( 2[8]( 3[5 , 5 , 6 , 9]));Map.is_bst := 3[5 , 5 , 6 , 9]( 3 [5 , 6]( 1[4 , 4 , 6]( 1[4 , 4 , 6 , 9]( 1 [4 , 6]( 2[8]( 2[4 , 8]( 1[5 , 8]( 0[7]( [list int))))))))))|}, 0, 4]: Map.bst * list int * in*)
 Definition s9 := Eval compute in step_checker s8 (Res (t_i:=t_i) t_func  t_atom  t_form  2((make 2 0%int63 .[ 0 <- 3%int63]) .[ 1 <-2%int63])%array).
Print s9.
(*s9 =({|Map.this :=( 0[7] ) 1[4 , 4 , 6]( 2[5 , 5 , 6]( 3[5 , 5 , 6 , 9]));Map.is_bst := 2 [5 , 5 , 6]( 3[5 , 5 , 6 , 9]( 3 [5 , 6]( 1[4 , 4 , 6]( 1[4 , 4 , 6 , 9]( 1[4 , 6]( 2[8]( 2[4 , 8]( 1[5 , 8]( 0[7]( [list int)))))))))))|}, 0, 4]: Map.bst * list int * in*)
 Definition s10 := Eval compute in step_checker s9 (Res (t_i:=t_i) t_func  t_atom  t_form  2((make 2 0%int63 .[ 0 <- 1%int63]) .[ 1 <-2%int63])%array).
Print s10.
(*s10 =({|Map.this :=( 0[7] ) 1[4 , 4 , 6]( 2[4 , 5 , 6]( 3[5 , 5 , 6 , 9]));Map.is_bst := 2 [4 , 5 , 6]( 2 [5 , 5 , 6]( 3[5 , 5 , 6 , 9]( 3 [5 , 6]( 1[4 , 4 , 6]( 1[4 , 4 , 6 , 9]( 1[4 , 6]( 2[8]( 2[4 , 8]( 1[5 , 8]( 0[7]( [list int))))))))))))|}, 0, 4]: Map.bst * list int * in*)
 Definition s11 := Eval compute in step_checker s10 (Res (t_i:=t_i) t_func  t_atom  t_form  0((make 2 0%int63 .[ 0 <- 2%int63]) .[ 1 <-0%int63])%array).
Print s11.
(*s11 =({|Map.this :=( 0[4 , 5] ) 1[4 , 4 , 6]( 2[4 , 5 , 6]( 3[5 , 5 , 6 , 9]));Map.is_bst := 0 [4 , 5]( 2 [4 , 5 , 6]( 2[5 , 5 , 6]( 3[5 , 5 , 6 , 9]( 3 [5 , 6]( 1[4 , 4 , 6]( 1[4 , 4 , 6 , 9]( 1[4 , 6]( 2[8]( 2[4 , 8]( 1[5 , 8]( 0[7]( [list int)))))))))))))|}, 0, 4]: Map.bst * list int * in*)