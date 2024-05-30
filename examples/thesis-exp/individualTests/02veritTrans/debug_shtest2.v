
(** studying shtest2 **)
Add Rec LoadPath "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/src" as SMTCoq.
From SMTCoq Require Import SMTCoq.
Require Import Bool PArray Int63 List ZArith.
Local Open Scope int63_scope.
Open Scope Z_scope.
Set Printing Depth 250.
Module shtest2.
Section shtest2.
Parse_certif_verit t_i t_func t_atom t_form root used_roots trace "shtest2.smt2" "shtest2.pf".
Compute @Euf_Checker.checker t_i t_func t_atom t_form root used_roots trace.
Compute (Form.check_form t_form && Atom.check_atom t_atom && Atom.wt t_i t_func t_atom).
Definition nclauses := Eval compute in let (nclauses, _, _) := trace in nclauses.
Print trace.
Definition s0 := Eval compute in (add_roots (S.make nclauses) root used_roots).
 Definition s1 := Eval compute in step_checker s0 (BuildDef (t_i:=t_i) t_func  t_atom  t_form  2 8).
Print s1.
(*s1 =({|Map.this := 0[5]( 1[6]( 2[5 , 7 , 8]));Map.is_bst := 2 [5 , 7 , 8]( 1 [6]( 0 [5]( [list int))))|}, 0, 6]: Map.bst * list int * in*)
 Definition s2 := Eval compute in step_checker s1 (BuildDef (t_i:=t_i) t_func  t_atom  t_form  3 12).
Print s2.
(*s2 =({|Map.this :=( 0[5] ) 1[6]( 2[5 , 7 , 8]( 3[4 , 7 , 12]));Map.is_bst := 3 [4 , 7 , 12]( 2 [5 , 7 , 8]( 1 [6]( 0 [5]( [list int)))))|}, 0, 6]: Map.bst * list int * in*)
 Definition s3 := Eval compute in step_checker s2 (Res (t_i:=t_i) t_func  t_atom  t_form  2((make 2 0%int63 .[ 0 <- 3%int63]) .[ 1 <- 2%int63])%array).
Print s3.
(*s3 =({|Map.this :=( 0[5] ) 1[6]( 2[7 , 8 , 12]( 3[4 , 7 , 12]));Map.is_bst := 2 [7 , 8 , 12]( 3[4 , 7 , 12]( 2[5 , 7 , 8]( 1 [6]( 0 [5]( [list int))))))|}, 0, 6]: Map.bst * list int * in*)
 Definition s4 := Eval compute in step_checker s3 (BuildDef2 (t_i:=t_i) t_func  t_atom  t_form  3 8).
Print s4.
(*s4 =({|Map.this :=( 0[5] ) 1[6]( 2[7 , 8 , 12]( 3[4 , 6 , 8]));Map.is_bst := 3 [4 , 6 , 8]( 2[7 , 8 , 12]( 3[4 , 7 , 12]( 2[5 , 7 , 8]( 1 [6]( 0[5] ( [list int)))))))|}, 0, 6]: Map.bst * list int * in*)
 Definition s5 := Eval compute in step_checker s4 (BuildDef (t_i:=t_i) t_func  t_atom  t_form  4 14).
Print s5.
(*s5 =({|Map.this :=( 0[5] ) 1[6]( 2[7 , 8 , 12]( 3[4 , 6 , 8]( 4[5 , 6 , 14])));Map.is_bst := 4 [5 , 6 , 14]( 3 [4 , 6 , 8]( 2[7 , 8 , 12]( 3[4 , 7 , 12]( 2[5 , 7 , 8]( 1[6]( 0[5]( [list int))))))))|}, 0, 6]: Map.bst * list int * in*)
 Definition s6 := Eval compute in step_checker s5 (Res (t_i:=t_i) t_func  t_atom  t_form  3((make 2 0%int63 .[ 0 <- 4%int63]) .[ 1 <- 3%int63])%array).
Print s6.
(*s6 =({|Map.this :=( 0[5] ) 1[6]( 2[7 , 8 , 12]( 3[6 , 8 , 14]( 4[5 , 6 , 14])));Map.is_bst := 3 [6 , 8 , 14]( 4[5 , 6 , 14]( 3[4 , 6 , 8]( 2[7 , 8 , 12]( 3[4 , 7 , 12]( 2[5 , 7 , 8]( 1[6]( 0[5]( [list int)))))))))|}, 0, 6]: Map.bst * list int * in*)
 Definition s7 := Eval compute in step_checker s6 (Res (t_i:=t_i) t_func  t_atom  t_form  3((make 2 0%int63 .[ 0 <- 2%int63]) .[ 1 <- 3%int63])%array).
Print s7.
(*s7 =({|Map.this :=( 0[5] ) 1[6]( 2[7 , 8 , 12]( 3[8 , 12 , 14]( 4[5 , 6 , 14])));Map.is_bst := 3 [8 , 12 , 14]( 3[6 , 8 , 14]( 4[5 , 6 , 14]( 3[4 , 6 , 8]( 2[7 , 8 , 12]( 3[4 , 7 , 12]( 2[5 , 7 , 8]( 1[6]( 0[5]( [list int))))))))))|}, 0, 6]: Map.bst * list int * in*)
 Definition s8 := Eval compute in step_checker s7 (BuildDef (t_i:=t_i) t_func  t_atom  t_form  2 10).
Print s8.
(*s8 =({|Map.this :=( 0[5] ) 1[6]( 2[5 , 10]( 3[8 , 12 , 14]( 4[5 , 6 , 14])));Map.is_bst := 2 [5 , 10]( 3[8 , 12 , 14]( 3[6 , 8 , 14]( 4[5 , 6 , 14]( 3[4 , 6 , 8]( 2[7 , 8 , 12]( 3[4 , 7 , 12]( 2[5 , 7 , 8]( 1[6]( 0[5]( [list int)))))))))))|}, 0, 6]: Map.bst * list int * in*)
 Definition s9 := Eval compute in step_checker s8 (BuildDef2 (t_i:=t_i) t_func  t_atom  t_form  4 10).
Print s9.
(*s9 =({|Map.this :=( 0[5] ) 1[6]( 2[5 , 10]( 3[8 , 12 , 14]( 4[4 , 10] ))3);Map.is_bst := 4 [4 , 10]( 2 [5 , 10]( 3[8 , 12 , 14]( 3[6 , 8 , 14]( 4[5 , 6 , 14]( 3[4 , 6 , 8]( 2[7 , 8 , 12]( 3[4 , 7 , 12]( 2[5 , 7 , 8]( 1[6]( 0[5]( [list int))))))))))))|}, 0, 6]: Map.bst * list int * in*)
 Definition s10 := Eval compute in step_checker s9 (Res (t_i:=t_i) t_func  t_atom  t_form  4((make 2 0%int63 .[ 0 <- 2%int63]) .[ 1 <-4%int63])%array).
Print s10.
(*s10 =({|Map.this :=( 0[5] ) 1[6]( 2[5 , 10]( 3[8 , 12 , 14]( 4[10] )));Map.is_bst := 4 [10]( 4 [4 , 10]( 2 [5 , 10]( 3[8 , 12 , 14]( 3[6 , 8 , 14]( 4[5 , 6 , 14]( 3[4 , 6 , 8]( 2[7 , 8 , 12]( 3[4 , 7 , 12]( 2[5 , 7 , 8]( 1[6]( 0[5]( [list int)))))))))))))|}, 0, 6]: Map.bst * list int * in*)
 Definition s11 := Eval compute in step_checker s10 (BuildDef (t_i:=t_i) t_func  t_atom  t_form  2 9).
Print s11.
(*s11 =({|Map.this :=( 0[5] ) 1[6]( 2[5 , 6 , 9]( 3[8 , 12 , 14]( 4[10] )));Map.is_bst := 2 [5 , 6 , 9]( 4 [10]( 4 [4 , 10]( 2 [5 , 10]( 3[8 , 12 , 14]( 3[6 , 8 , 14]( 4[5 , 6 , 14]( 3[4 , 6 , 8]( 2[7 , 8 , 12]( 3[4 , 7 , 12]( 2[5 , 7 , 8]( 1[6]( 0[5]([list int))))))))))))))|}, 0, 6]: Map.bst * list int * in*)
 Definition s12 := Eval compute in step_checker s11 (Res (t_i:=t_i) t_func  t_atom  t_form  2((make 2 0%int63 .[ 0 <- 2%int63]).[ 1 <- 3%int63])%array).
Print s12.
(*s12 =({|Map.this :=( 0[5] ) 1[6]( 2[5 , 6 , 12 , 14]( 3[8 , 12 , 14]( 4[10] )));Map.is_bst := 2[5 , 6 , 12 , 14]( 2 [5 , 6 , 9]( 4 [10]( 4 [4 , 10]( 2 [5 , 10]( 3[8 , 12 , 14]( 3[6 , 8 , 14]( 4[5 , 6 , 14]( 3[4 , 6 , 8]( 2[7 , 8 , 12]( 3[4 , 7 , 12]( 2[5 , 7 , 8]( 1[6]( 0[5]([list int)))))))))))))))|}, 0, 6]: Map.bst * list int * in*)
 Definition s13 := Eval compute in step_checker s12 (BuildDef (t_i:=t_i) t_func  t_atom t_form  5 11).
Print s13.
(*s13 =({|Map.this :=( 0[5] ) 1[6](( 2[5 , 6 , 12 , 14]) 3[8 , 12 , 14]( 4[10]( 5[4 , 5 , 11])));Map.is_bst := 5 [4 , 5 , 11]( 2[5 , 6 , 12 , 14]( 2[5 , 6 , 9]( 4 [10]( 4 [4 , 10]( 2[5 , 10]( 3[8 , 12 , 14]( 3[6 , 8 , 14]( 4[5 , 6 , 14]( 3[4 , 6 , 8]( 2[7 , 8 , 12]( 3[4, 7 , 12]( 2[5, 7 , 8]( 1[6]( 0[5]([list int))))))))))))))))|}, 0, 6]: Map.bst * list int * in*)
 Definition s14 := Eval compute in step_checker s13 (Res (t_i:=t_i) t_func  t_atom  t_form 5((make 2 0%int63 .[ 0 <- 5%int63]).[ 1 <- 4%int63])%array).
Print s14.
(*s14 =({|Map.this :=( 0[5] ) 1[6](( 2[5 , 6 , 12 , 14]) 3[8 , 12 , 14]( 4[10]( 5[4 , 5] )))4;Map.is_bst := 5 [4 , 5]( 5[4 , 5 , 11]( 2[5 , 6 , 12 , 14]( 2[5 , 6 , 9]( 4 [10]( 4[4 , 10]( 2[5 , 10]( 3[8 , 12 , 14]( 3[6 , 8 , 14]( 4[5 , 6 , 14]( 3[4 , 6 , 8]( 2[7, 8 , 12]( 3[4, 7 , 12]( 2[5,7 , 8]( 1[6](0[5]([list int)))))))))))))))))|}, 0, 6]: Map.bst * list int * in*)
 Definition s15 := Eval compute in step_checker s14 (Res (t_i:=t_i) t_func  t_atom t_form  5((make 2 0%int63 .[ 0 <-2%int63]) .[ 1 <- 5%int63])%array).
Print s15.
(*s15 =({|Map.this :=( 0[5] ) 1[6](( 2[5 , 6 , 12 , 14]) 3[8 , 12 , 14]( 4[10]( 5[5 , 6 , 12 , 14])));Map.is_bst := 5[5 , 6 , 12 , 14]( 5 [4 , 5]( 5[4 , 5 , 11]( 2[5 , 6 , 12 , 14]( 2[5 , 6 , 9]( 4[10]( 4[4 , 10]( 2[5 , 10]( 3[8 , 12 , 14]( 3[6 , 8 , 14]( 4[5 , 6 , 14]( 3[4 , 6 , 8]( 2[7, 8 , 12]( 3[4,7 , 12]( 2[5,7 , 8](1[6](0[5]([list int))))))))))))))))))|}, 0, 6]: Map.bst * list int * in*)
 Definition s16 := Eval compute in step_checker s15 (BuildDef2 (t_i:=t_i) t_func t_atom  t_form  2 8).
Print s16.
(*s16 =({|Map.this :=( 0[5] ) 1[6](( 2[4 , 6 , 8]) 3[8 , 12 , 14]( 4[10]( 5[5 , 6 , 12 , 14])));Map.is_bst := 2 [4 , 6 , 8]( 5[5 , 6 , 12 , 14]( 5 [4 , 5]( 5[4 , 5 , 11]( 2[5 , 6 , 12 , 14]( 2[5 , 6 , 9]( 4[10]( 4[4 , 10]( 2[5 , 10]( 3[8 , 12 , 14]( 3[6 , 8 , 14]( 4[5, 6 , 14]( 3[4, 6 , 8]( 2[7,8 , 12]( 3[4,7 ,12](2[5,7 , 8](1[6](0[5]([list int)))))))))))))))))))|}, 0, 6]: Map.bst * list int * in*)
 Definition s17 := Eval compute in step_checker s16 (Res (t_i:=t_i) t_func  t_atom t_form  2((make 2 0%int63 .[ 0 <-5%int63]) .[ 1 <- 2%int63])%array).
Print s17.
(*s17 =({|Map.this :=( 0[5] ) 1[6](( 2[6 , 8 , 12 , 14]) 3[8 , 12 , 14]( 4[10]( 5[5 , 6 , 12 , 14])));Map.is_bst := 2[6 , 8 , 12 , 14]( 2 [4 , 6 , 8]( 5[5 , 6 , 12 , 14]( 5 [4 , 5]( 5[4 , 5 , 11]( 2[5 , 6 , 12 , 14]( 2[5 , 6 , 9]( 4[10]( 4[4 , 10]( 2[5 , 10]( 3[8 , 12 , 14]( 3[6, 8 , 14]( 4[5, 6 , 14]( 3[4,6 , 8]( 2[7,8 ,12](3[4,7 ,12](2[5,7 , 8](1[6](0[5]([list int))))))))))))))))))))|}, 0, 6]: Map.bst * list int * in*)
 Definition s18 := Eval compute in step_checker s17 (BuildDef2 (t_i:=t_i) t_func t_atom  t_form  5 9).
Print s18.
(*s18 =({|Map.this :=( 0[5] ) 1[6](( 2[6 , 8 , 12 , 14]) 3[8 , 12 , 14]( 4[10]( 5[4 , 7 , 9])));Map.is_bst := 5 [4 , 7 , 9]( 2[6 , 8 , 12 , 14]( 2[4 , 6 , 8]( 5[5 , 6 , 12 , 14]( 5 [4 , 5]( 5[4 , 5 , 11]( 2[5 , 6 , 12 , 14]( 2[5 , 6 , 9]( 4[10]( 4[4 , 10]( 2[5 , 10]( 3[8, 12 , 14]( 3[6, 8 , 14]( 4[5,6 , 14]( 3[4,6 , 8](2[7,8 ,12](3[4,7 ,12](2[5,7 , 8](1[6](0[5]([list int)))))))))))))))))))))|}, 0, 6]: Map.bst * list int * in*)
 Definition s19 := Eval compute in step_checker s18 (Res (t_i:=t_i) t_func  t_atom t_form  3((make 2 0%int63 .[ 0 <-5%int63]) .[ 1 <- 3%int63])%array).
Print s19.
(*s19 =({|Map.this :=( 0[5] ) 1[6](( 2[6 , 8 , 12 , 14]) 3[4 , 7 , 12 , 14]( 4[10]( 5[4 , 7 , 9])));Map.is_bst := 3[4 , 7 , 12 , 14]( 5 [4 , 7 , 9]( 2[6 , 8 , 12 , 14]( 2[4 , 6 , 8]( 5[5 , 6 , 12 , 14]( 5[4 , 5]( 5[4 , 5 , 11]( 2[5, 6 , 12 , 14]( 2[5 , 6 , 9]( 4[10]( 4[4 , 10]( 2[5 , 10]( 3[8, 12 , 14]( 3[6,8 , 14]( 4[5,6 ,14](3[4,6 , 8](2[7,8 ,12](3[4,7 ,12](2[5,7 , 8](1[6](0[5]([list int))))))))))))))))))))))|}, 0, 6]: Map.bst * list int * in*)
 Definition s20 := Eval compute in step_checker s19 (BuildDef2 (t_i:=t_i) t_func t_atom  t_form  5 11).
Print s20.
(*s20 =({|Map.this :=( 0[5] ) 1[6](( 2[6 , 8 , 12 , 14]) 3[4 , 7 , 12 , 14]( 4[10]( 5[4 , 5 , 11])));Map.is_bst := 5 [4 , 5 , 11]( 3[4 , 7 , 12 , 14]( 5[4 , 7 , 9]( 2[6 , 8 , 12 , 14]( 2[4 , 6 , 8]( 5[5 , 6 , 12 , 14]( 5[4 , 5]( 5[4 , 5 , 11]( 2[5, 6 , 12 , 14]( 2[5 , 6 , 9]( 4[10]( 4[4 , 10]( 2[5 , 10]( 3[8,12 , 14]( 3[6,8 ,14](4[5,6 ,14](3[4,6 , 8](2[7,8 ,12](3[4,7 ,12](2[5,7 , 8](1[6](0[5]([list int)))))))))))))))))))))))|}, 0, 6]: Map.bst * list int * in*)
 Definition s21 := Eval compute in step_checker s20 (Res (t_i:=t_i) t_func  t_atom t_form  4((make 2 0%int63 .[ 0 <-5%int63]) .[ 1 <- 4%int63])%array).
Print s21.
(*s21 =({|Map.this :=( 0[5] ) 1[6](( 2[6 , 8 , 12 , 14]) 3[4 , 7 , 12 , 14]( 4[4 , 5]( 5[4 , 5 , 11])));Map.is_bst := 4 [4 , 5]( 5[4 , 5 , 11]( 3[4 , 7 , 12 , 14]( 5[4 , 7 , 9]( 2[6 , 8 , 12 , 14]( 2[4 , 6 , 8]( 5[5 , 6 , 12 , 14]( 5[4 , 5]( 5[4 , 5 , 11]( 2[5, 6 , 12 , 14]( 2[5 , 6 , 9]( 4[10]( 4[4 , 10]( 2[5 , 10]( 3[8,12 ,14](3[6,8 ,14](4[5,6 ,14](3[4,6 , 8](2[7,8 ,12](3[4,7 ,12](2[5,7 , 8](1[6](0[5]([list int))))))))))))))))))))))))|}, 0, 6]: Map.bst * list int * in*)
 Definition s22 := Eval compute in step_checker s21 (Res (t_i:=t_i) t_func  t_atom t_form  4((make 2 0%int63 .[ 0 <-3%int63]) .[ 1 <- 4%int63])%array).
Print s22.
(*s22 =({|Map.this :=( 0[5] ) 1[6](( 2[6 , 8 , 12 , 14]) 3[4 , 7 , 12 , 14]( 4[4 , 5 , 0]( 5[4 , 5 , 11])));Map.is_bst := 4 [4 , 5 , 0]( 4 [4 , 5]( 5[4 , 5 , 11]( 3[4 , 7 , 12 , 14]( 5[4 , 7 , 9]( 2[6 , 8 , 12 , 14]( 2[4 , 6 , 8]( 5[5, 6 , 12 , 14]( 5[4 , 5]( 5[4 , 5 , 11]( 2[5, 6, 12 , 14]( 2[5 , 6 , 9]( 4[10]( 4[4 , 10]( 2[5 , 10](3[8,12 ,14](3[6,8 ,14](4[5,6 ,14](3[4,6 , 8](2[7,8 ,12](3[4,7 ,12](2[5,7 , 8](1[6](0[5]([list int)))))))))))))))))))))))))|}, 0, 6]: Map.bst * list int * in*)
(* ====> ":: 0%int63 " in output found, break *)
Definition confl := Eval compute in let (_, _, confl) := trace in confl.
Compute (C.is_false (S.get s22 confl)).