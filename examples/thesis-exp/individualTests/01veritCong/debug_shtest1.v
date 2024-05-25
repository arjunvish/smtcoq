
(** studying shtest1 **)
Add Rec LoadPath "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/src" as SMTCoq.
From SMTCoq Require Import SMTCoq.
Require Import Bool PArray Int63 List ZArith.
Local Open Scope int63_scope.
Open Scope Z_scope.
Set Printing Depth 250.
Module shtest1.
Section shtest1.
Parse_certif_verit t_i t_func t_atom t_form root used_roots trace "shtest1.smt2" "shtest1.pf".
Compute @Euf_Checker.checker t_i t_func t_atom t_form root used_roots trace.
Compute (Form.check_form t_form && Atom.check_atom t_atom && Atom.wt t_i t_func t_atom).
Definition nclauses := Eval compute in let (nclauses, _, _) := trace in nclauses.
Print trace.
Definition s0 := Eval compute in (add_roots (S.make nclauses) root used_roots).
 Definition s1 := Eval compute in step_checker s0 (BuildDef (t_i:=t_i) t_func  t_atom  t_form  1 12).
Print s1.
(*s1 =({|Map.this := 0[13]( 1[9 , 11 , 12]);Map.is_bst := 1 [9 , 11 , 12]( 0 [13]( [list int)))|}, 0, 8]: Map.bst * list int * in*)
 Definition s2 := Eval compute in step_checker s1 (BuildDef (t_i:=t_i) t_func  t_atom  t_form  2 28).
Print s2.
(*s2 =({|Map.this := 0[13]( 1[9 , 11 , 12]( 2[9 , 10 , 28]));Map.is_bst := 2 [9 , 10 , 28]( 1[9 , 11 , 12]( 0 [13]( [list int))))|}, 0, 8]: Map.bst * list int * in*)
 Definition s3 := Eval compute in step_checker s2 (Res (t_i:=t_i) t_func  t_atom  t_form  1((make 2 0%int63 .[ 0 <- 2%int63]) .[ 1 <- 1%int63])%array).
Print s3.
(*s3 =({|Map.this := 0[13]( 1[9 , 12 , 28]( 2[9 , 10 , 28]));Map.is_bst := 1 [9 , 12 , 28]( 2[9 , 10 , 28]( 1[9 , 11 , 12]( 0 [13]( [list int)))))|}, 0, 8]: Map.bst * list int * in*)
 Definition s4 := Eval compute in step_checker s3 (BuildDef2 (t_i:=t_i) t_func  t_atom  t_form  2 12).
Print s4.
(*s4 =({|Map.this := 0[13]( 1[9 , 12 , 28]( 2[8 , 10 , 12]));Map.is_bst := 2 [8 , 10 , 12]( 1[9 , 12 , 28]( 2[9 , 10 , 28]( 1[9 , 11 , 12]( 0 [13]( [list int))))))|}, 0, 8]: Map.bst * list int * in*)
 Definition s5 := Eval compute in step_checker s4 (BuildDef (t_i:=t_i) t_func  t_atom  t_form  3 30).
Print s5.
(*s5 =({|Map.this :=( 0[13] ) 1[9 , 12 , 28]( 2[8 , 10 , 12]( 3[8 , 11 , 30]));Map.is_bst := 3 [8 , 11 , 30]( 2[8 , 10 , 12]( 1[9 , 12 , 28]( 2[9 , 10 , 28]( 1[9 , 11 , 12]( 0[13] ( [list int)))))))|}, 0, 8]: Map.bst * list int * in*)
 Definition s6 := Eval compute in step_checker s5 (Res (t_i:=t_i) t_func  t_atom  t_form  2((make 2 0%int63 .[ 0 <- 3%int63]) .[ 1 <- 2%int63])%array).
Print s6.
(*s6 =({|Map.this :=( 0[13] ) 1[9 , 12 , 28]( 2[8 , 12 , 30]( 3[8 , 11 , 30]));Map.is_bst := 2 [8 , 12 , 30]( 3[8 , 11 , 30]( 2[8 , 10 , 12]( 1[9 , 12 , 28]( 2[9 , 10 , 28]( 1[9 , 11 , 12]( 0[13]( [list int))))))))|}, 0, 8]: Map.bst * list int * in*)
 Definition s7 := Eval compute in step_checker s6 (Res (t_i:=t_i) t_func  t_atom  t_form  2((make 2 0%int63 .[ 0 <- 1%int63]) .[ 1 <- 2%int63])%array).
Print s7.
(*s7 =({|Map.this :=( 0[13] ) 1[9 , 12 , 28]( 2[12 , 28 , 30]( 3[8 , 11 , 30]));Map.is_bst := 2 [12 , 28 , 30]( 2[8 , 12 , 30]( 3[8 , 11 , 30]( 2[8 , 10 , 12]( 1[9 , 12 , 28]( 2[9 , 10 , 28]( 1[9 , 11 , 12]( 0[13]( [list int)))))))))|}, 0, 8]: Map.bst * list int * in*)
 Definition s8 := Eval compute in step_checker s7 (BuildDef (t_i:=t_i) t_func  t_atom  t_form  1 13).
Print s8.
(*s8 =({|Map.this :=( 0[13] ) 1[8 , 11 , 13]( 2[12 , 28 , 30]( 3[8 , 11 , 30]));Map.is_bst := 1 [8 , 11 , 13]( 2[12 , 28 , 30]( 2[8 , 12 , 30]( 3[8 , 11 , 30]( 2[8 , 10 , 12]( 1[9 , 12 , 28]( 2[9 , 10 , 28]( 1[9 , 11 , 12]( 0[13]( [list int))))))))))|}, 0, 8]: Map.bst * list int * in*)
 Definition s9 := Eval compute in step_checker s8 (BuildDef2 (t_i:=t_i) t_func  t_atom  t_form  3 14).
Print s9.
(*s9 =({|Map.this :=( 0[13] ) 1[8 , 11 , 13]( 2[12 , 28 , 30]( 3[10 , 14] ));Map.is_bst := 3 [10 , 14]( 1[8 , 11 , 13]( 2[12 , 28 , 30]( 2[8 , 12 , 30]( 3[8 , 11 , 30]( 2[8 , 10 , 12]( 1[9 , 12 , 28]( 2[9 , 10 , 28]( 1[9 , 11 , 12]( 0[13]( [list int)))))))))))|}, 0, 8]: Map.bst * list int * in*)
 Definition s10 := Eval compute in step_checker s9 (BuildDef2 (t_i:=t_i) t_func  t_atom  t_form  4 16).
Print s10.
(*s10 =({|Map.this :=( 0[13] ) 1[8 , 11 , 13]( 2[12 , 28 , 30]( 3[10 , 14]( 4[12 , 14 , 16])));Map.is_bst := 4 [12 , 14 , 16]( 3 [10 , 14]( 1[8 , 11 , 13]( 2[12 , 28 , 30]( 2[8 , 12 , 30]( 3[8 , 11 , 30]( 2[8 , 10 , 12]( 1[9 , 12 , 28]( 2[9 , 10 , 28]( 1[9 , 11 , 12]( 0[13]( [list int))))))))))))|}, 0, 8]: Map.bst * list int * in*)
 Definition s11 := Eval compute in step_checker s10 (Res (t_i:=t_i) t_func  t_atom  t_form  3(((make 3 0%int63 .[ 0 <- 1%int63]).[ 1 <- 3%int63]) .[ 2 <- 4%int63])%array).
Print s11.
(*s11 =({|Map.this :=( 0[13] ) 1[8 , 11 , 13]( 2[12 , 28 , 30]( 3[8 , 14 , 16]( 4[12 , 14 , 16])));Map.is_bst := 3 [8 , 14 , 16]( 4[12 , 14 , 16]( 3 [10 , 14]( 1[8 , 11 , 13]( 2[12 , 28 , 30]( 2[8 , 12 , 30]( 3[8 , 11 , 30]( 2[8 , 10 , 12]( 1[9 , 12 , 28]( 2[9 , 10 , 28]( 1[9 , 11 , 12]( 0[13]( [list int)))))))))))))|}, 0, 8]: Map.bst * list int * in*)
 Definition s12 := Eval compute in step_checker s11 (BuildDef2 (t_i:=t_i) t_func  t_atom  t_form 1 12).
Print s12.
(*s12 =({|Map.this :=( 0[13] ) 1[8 , 10 , 12]( 2[12 , 28 , 30]( 3[8 , 14 , 16]( 4[12 , 14 , 16])));Map.is_bst := 1 [8 , 10 , 12]( 3[8 , 14 , 16]( 4[12 , 14 , 16]( 3 [10 , 14]( 1[8 , 11 , 13]( 2[12 , 28 , 30]( 2[8 , 12 , 30]( 3[8 , 11 , 30]( 2[8 , 10 , 12]( 1[9 , 12 , 28]( 2[9 , 10 , 28]( 1[9, 11 , 12]( 0[13]([list int))))))))))))))|}, 0, 8]: Map.bst * list int * in*)
 Definition s13 := Eval compute in step_checker s12 (BuildDef (t_i:=t_i) t_func  t_atom t_form  5 15).
Print s13.
(*s13 =({|Map.this :=( 0[13] ) 1[8 , 10 , 12](( 2[12 , 28 , 30]) 3[8 , 14 , 16]( 4[12 , 14 , 16]( 5[10 , 11 , 15])));Map.is_bst := 5 [10 , 11 , 15]( 1[8 , 10 , 12]( 3[8 , 14 , 16]( 4[12 , 14 , 16]( 3 [10 , 14]( 1[8 , 11 , 13]( 2[12 , 28 , 30]( 2[8 , 12 , 30]( 3[8 , 11 , 30]( 2[8 , 10 , 12]( 1[9 , 12 , 28]( 2[9, 10 , 28]( 1[9, 11 , 12]( 0[13]([list int)))))))))))))))|}, 0, 8]: Map.bst * list int * in*)
 Definition s14 := Eval compute in step_checker s13 (BuildDef (t_i:=t_i) t_func  t_atom t_form  6 16).
Print s14.
(*s14 =({|Map.this :=(( 0[13] ) 1[8 , 10 , 12]( 2[12 , 28 , 30])) 3[8 , 14 , 16]( 4[12 , 14 , 16]( 5[10 , 11 , 15]( 6[13 , 15 , 16])));Map.is_bst := 6 [13 , 15 , 16]( 5[10 , 11 , 15]( 1[8 , 10 , 12]( 3[8 , 14 , 16]( 4[12 , 14 , 16]( 3[10 , 14]( 1[8 , 11 , 13]( 2[12 , 28 , 30]( 2[8 , 12 , 30]( 3[8 , 11 , 30]( 2[8 , 10 , 12]( 1[9, 12 , 28]( 2[9, 10 , 28]( 1[9,11 , 12]( 0[13]([list int))))))))))))))))|}, 0, 8]: Map.bst * list int * in*)
 Definition s15 := Eval compute in step_checker s14 (Res (t_i:=t_i) t_func  t_atom t_form  5(((make 3 0%int63 .[ 0 <-1%int63]) .[ 1 <- 5%int63]).[ 2 <- 6%int63])%array).
Print s15.
(*s15 =({|Map.this :=(( 0[13] ) 1[8 , 10 , 12]( 2[12 , 28 , 30])) 3[8 , 14 , 16]( 4[12 , 14 , 16]( 5[8, 10, 11 , 0 , 15 , 16]( 6[13 , 15 , 16])));Map.is_bst := 5[8, 10 , 11 , 0 , 15 , 16]( 6[13 , 15 , 16]( 5[10 , 11 , 15]( 1[8 , 10 , 12]( 3[8 , 14 , 16]( 4[12 , 14 , 16]( 3[10 , 14]( 1[8 , 11 , 13]( 2[12 , 28 , 30]( 2[8 , 12 , 30]( 3[8 , 11 , 30]( 2[8, 10 , 12]( 1[9, 12 , 28]( 2[9,10 , 28]( 1[9,11 ,12](0[13]([list int)))))))))))))))))|}, 0, 8]: Map.bst * list int * in*)
(* ====> ":: 0%int63 " in output found, break *)
Definition confl := Eval compute in let (_, _, confl) := trace in confl.
Compute (C.is_false (S.get s15 confl)).