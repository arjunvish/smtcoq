
(** studying shtest2min **)
Add Rec LoadPath "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/src" as SMTCoq.
From SMTCoq Require Import SMTCoq.
Require Import Bool PArray Int63 List ZArith.
Local Open Scope int63_scope.
Open Scope Z_scope.
Set Printing Depth 250.
Module shtest2min.
Section shtest2min.
Parse_certif_verit t_i t_func t_atom t_form root used_roots trace "shtest2min.smt2" "shtest2min.pf".
Compute @Euf_Checker.checker t_i t_func t_atom t_form root used_roots trace.
Compute (Form.check_form t_form && Atom.check_atom t_atom && Atom.wt t_i t_func t_atom).
Definition nclauses := Eval compute in let (nclauses, _, _) := trace in nclauses.
Print trace.
Definition s0 := Eval compute in (add_roots (S.make nclauses) root used_roots).
 Definition s1 := Eval compute in step_checker s0 (BuildDef (t_i:=t_i) t_func  t_atom  t_form  3 9).
Print s1.
(*s1 =({|Map.this :=( 0[8] ) 1[10]( 2[9]( 3[5 , 6 , 9]));Map.is_bst := 3 [5 , 6 , 9]( 2 [9]( 1 [10]( 0 [8]( [list int)))))|}, 0, 5]: Map.bst * list int * in*)
 Definition s2 := Eval compute in step_checker s1 (Res (t_i:=t_i) t_func  t_atom  t_form  3((make 2 0%int63 .[ 0 <- 3%int63]) .[ 1 <- 0%int63])%array).
Print s2.
(*s2 =({|Map.this :=( 0[8] ) 1[10]( 2[9]( 3[5 , 6] ));Map.is_bst := 3 [5 , 6]( 3 [5 , 6 , 9]( 2 [9]( 1 [10]( 0 [8]( [list int))))))|}, 0, 5]: Map.bst * list int * in*)
 Definition s3 := Eval compute in step_checker s2 (BuildDef (t_i:=t_i) t_func  t_atom  t_form  4 11).
Print s3.
(*s3 =({|Map.this :=( 0[8] ) 1[10]( 2[9]( 3[5 , 6]( 4[4 , 5 , 11])));Map.is_bst := 4 [4 , 5 , 11]( 3 [5 , 6]( 3[5 , 6 , 9]( 2 [9]( 1 [10]( 0[8] ( [list int)))))))|}, 0, 5]: Map.bst * list int * in*)
 Definition s4 := Eval compute in step_checker s3 (Res (t_i:=t_i) t_func  t_atom  t_form  4((make 2 0%int63 .[ 0 <- 4%int63]) .[ 1 <- 1%int63])%array).
Print s4.
(*s4 =({|Map.this :=( 0[8] ) 1[10]( 2[9]( 3[5 , 6]( 4[4 , 5] )))4;Map.is_bst := 4 [4 , 5]( 4[4 , 5 , 11]( 3 [5 , 6]( 3[5 , 6 , 9]( 2 [9]( 1[10]( 0[8]( [list int))))))))|}, 0, 5]: Map.bst * list int * in*)
 Definition s5 := Eval compute in step_checker s4 (Res (t_i:=t_i) t_func  t_atom  t_form  4((make 2 0%int63 .[ 0 <- 3%int63]) .[ 1 <- 4%int63])%array).
Print s5.
(*s5 =({|Map.this :=( 0[8] ) 1[10]( 2[9]( 3[5 , 6]( 4[5 , 6] )))4;Map.is_bst := 4 [5 , 6]( 4 [4 , 5]( 4[4 , 5 , 11]( 3 [5 , 6]( 3[5 , 6 , 9]( 2[9]( 1[10]( 0[8]( [list int)))))))))|}, 0, 5]: Map.bst * list int * in*)
 Definition s6 := Eval compute in step_checker s5 (BuildDef2 (t_i:=t_i) t_func  t_atom  t_form  3 8).
Print s6.
(*s6 =({|Map.this :=( 0[8] ) 1[10]( 2[9]( 3[4 , 6 , 8]( 4[5 , 6] )))4;Map.is_bst := 3 [4 , 6 , 8]( 4 [5 , 6]( 4 [4 , 5]( 4[4 , 5 , 11]( 3 [5 , 6]( 3[5 , 6 , 9]( 2[9]( 1[10]( 0[8]( [list int))))))))))|}, 0, 5]: Map.bst * list int * in*)
 Definition s7 := Eval compute in step_checker s6 (Res (t_i:=t_i) t_func  t_atom  t_form  3((make 2 0%int63 .[ 0 <- 4%int63]) .[ 1 <- 3%int63])%array).
Print s7.
(*s7 =({|Map.this :=( 0[8] ) 1[10]( 2[9]( 3[6 , 8]( 4[5 , 6] )))4;Map.is_bst := 3 [6 , 8]( 3 [4 , 6 , 8]( 4 [5 , 6]( 4 [4 , 5]( 4[4 , 5 , 11]( 3[5 , 6]( 3[5 , 6 , 9]( 2[9]( 1[10]( 0[8]( [list int)))))))))))|}, 0, 5]: Map.bst * list int * in*)
 Definition s8 := Eval compute in step_checker s7 (BuildDef2 (t_i:=t_i) t_func  t_atom  t_form  4 9).
Print s8.
(*s8 =({|Map.this :=( 0[8] ) 1[10]( 2[9]( 3[6 , 8]( 4[4 , 7 , 9])));Map.is_bst := 4 [4 , 7 , 9]( 3 [6 , 8]( 3[4 , 6 , 8]( 4 [5 , 6]( 4 [4 , 5]( 4[4 , 5 , 11]( 3[5 , 6]( 3[5 , 6 , 9]( 2[9]( 1[10]( 0[8]( [list int))))))))))))|}, 0, 5]: Map.bst * list int * in*)
 Definition s9 := Eval compute in step_checker s8 (Res (t_i:=t_i) t_func  t_atom  t_form  0((make 2 0%int63 .[ 0 <- 4%int63]) .[ 1 <-0%int63])%array).
Print s9.
(*s9 =({|Map.this :=( 0[4 , 7] ) 1[10]( 2[9]( 3[6 , 8]( 4[4 , 7 , 9])));Map.is_bst := 0 [4 , 7]( 4 [4 , 7 , 9]( 3 [6 , 8]( 3[4 , 6 , 8]( 4 [5 , 6]( 4[4 , 5]( 4[4 , 5 , 11]( 3[5 , 6]( 3[5 , 6 , 9]( 2[9]( 1[10]( 0[8]( [list int)))))))))))))|}, 0, 5]: Map.bst * list int * in*)
 Definition s10 := Eval compute in step_checker s9 (BuildDef2 (t_i:=t_i) t_func  t_atom  t_form  4 11).
Print s10.
(*s10 =({|Map.this :=( 0[4 , 7] ) 1[10]( 2[9]( 3[6 , 8]( 4[4 , 5 , 11])));Map.is_bst := 4 [4 , 5 , 11]( 0 [4 , 7]( 4[4 , 7 , 9]( 3 [6 , 8]( 3[4 , 6 , 8]( 4[5 , 6]( 4[4 , 5]( 4[4 , 5 , 11]( 3[5 , 6]( 3[5 , 6 , 9]( 2[9]( 1[10]( 0[8]([list int))))))))))))))|}, 0, 5]: Map.bst * list int * in*)
 Definition s11 := Eval compute in step_checker s10 (Res (t_i:=t_i) t_func  t_atom  t_form  1((make 2 0%int63 .[ 0 <- 4%int63]) .[ 1 <-1%int63])%array).
Print s11.
(*s11 =({|Map.this :=( 0[4 , 7] ) 1[4 , 5]( 2[9]( 3[6 , 8]( 4[4 , 5 , 11])));Map.is_bst := 1 [4 , 5]( 4[4 , 5 , 11]( 0 [4 , 7]( 4[4 , 7 , 9]( 3 [6 , 8]( 3[4 , 6 , 8]( 4[5 , 6]( 4[4 , 5]( 4[4 , 5 , 11]( 3[5 , 6]( 3[5 , 6 , 9]( 2[9]( 1[10]( 0[8]([list int)))))))))))))))|}, 0, 5]: Map.bst * list int * in*)
 Definition s12 := Eval compute in step_checker s11 (Res (t_i:=t_i) t_func  t_atom  t_form  1((make 2 0%int63 .[ 0 <- 0%int63]).[ 1 <- 1%int63])%array).
Print s12.
(*s12 =({|Map.this :=( 0[4 , 7] ) 1[4 , 5 , 0]( 2[9]( 3[6 , 8]( 4[4 , 5 , 11])));Map.is_bst := 1 [4 , 5 , 0]( 1 [4 , 5]( 4[4 , 5 , 11]( 0 [4 , 7]( 4[4 , 7 , 9]( 3[6 , 8]( 3[4 , 6 , 8]( 4[5 , 6]( 4[4 , 5]( 4[4 , 5 , 11]( 3[5 , 6]( 3[5 , 6 , 9]( 2[9]( 1[10]( 0[8]([list int))))))))))))))))|}, 0, 5]: Map.bst * list int * in*)
(* ====> ":: 0%int63 " in output found, break *)
Definition confl := Eval compute in let (_, _, confl) := trace in confl.
Compute (C.is_false (S.get s12 confl)).