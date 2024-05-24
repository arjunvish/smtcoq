
(** studying test7cvc5 **)
Add Rec LoadPath "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/src" as SMTCoq.
From SMTCoq Require Import SMTCoq.
Require Import Bool PArray Int63 List ZArith.
Local Open Scope int63_scope.
Open Scope Z_scope.
Set Printing Depth 250.
Module test7cvc5.
Section test7cvc5.
Parse_certif_verit t_i t_func t_atom t_form root used_roots trace "test7cvc5.smt2" "test7cvc5.pf".
Compute @Euf_Checker.checker t_i t_func t_atom t_form root used_roots trace.
Compute (Form.check_form t_form && Atom.check_atom t_atom && Atom.wt t_i t_func t_atom).
Definition nclauses := Eval compute in let (nclauses, _, _) := trace in nclauses.
Print trace.
Definition s0 := Eval compute in (add_roots (S.make nclauses) root used_roots).
 Definition s1 := Eval compute in step_checker s0 (BuildDef2 (t_i:=t_i) t_func  t_atom  t_form  1 41).
Print s1.
(*s1 =({|Map.this := 0[31]( 1[30 , 39 , 41]);Map.is_bst := 1 [30 , 39 , 41]( 0 [31]( [list int)))|}, 0, 10]: Map.bst * list int * in*)
 Definition s2 := Eval compute in step_checker s1 (LiaMicromega (t_i:=t_i) t_func  t_atom  t_form  2 (46%int63 :: nil) nil).
Print s2.
(*s2 =({|Map.this := 0[31]( 1[30 , 39 , 41]( 2[46] ));Map.is_bst := 2 [46]( 1[30 , 39 , 41]( 0 [31]( [list int))))|}, 0, 10]: Map.bst * list int * in*)
 Definition s3 := Eval compute in step_checker s2 (LiaMicromega (t_i:=t_i) t_func  t_atom  t_form  3 (48%int63 :: nil) nil).
Print s3.
(*s3 =({|Map.this :=( 0[31] ) 1[30 , 39 , 41]( 2[46]( 3[48] ));Map.is_bst := 3 [48]( 2 [46]( 1[30 , 39 , 41]( 0 [31]( [list int)))))|}, 0, 10]: Map.bst * list int * in*)
 Definition s4 := Eval compute in step_checker s3 (EqTr (t_i:=t_i) t_func  t_atom  t_form  4 50(49%int63 :: 9%int63 :: 47%int63 :: nil)).
Print s4.
(*s4 =({|Map.this :=( 0[31] ) 1[30 , 39 , 41]( 2[46]( 3[48]( 4[9 , 47 , 49 , 50])));Map.is_bst := 4[9 , 47 , 49 , 50]( 3 [48]( 2 [46]( 1[30 , 39 , 41]( 0 [31]( [list int))))))|}, 0, 10]: Map.bst * list int * in*)
 Definition s5 := Eval compute in step_checker s4 (BuildDef2 (t_i:=t_i) t_func  t_atom  t_form  5 52).
Print s5.
(*s5 =({|Map.this :=( 0[31] ) 1[30 , 39 , 41](( 2[46] ) 3[48]( 4[9 , 47 , 49 , 50]( 5[8 , 50 , 52])));Map.is_bst := 5 [8 , 50 , 52]( 4[9 , 47 , 49 , 50]( 3 [48]( 2 [46]( 1[30 , 39 , 41]( 0[31] ( [list int)))))))|}, 0, 10]: Map.bst * list int * in*)
 Definition s6 := Eval compute in step_checker s5 (Res (t_i:=t_i) t_func  t_atom  t_form  5((make 2 0%int63 .[ 0 <- 4%int63]) .[ 1 <- 5%int63])%array).
Print s6.
(*s6 =({|Map.this :=( 0[31] ) 1[30 , 39 , 41](( 2[46] ) 3[48]( 4[9 , 47 , 49 , 50]( 5[47 , 49 , 50 , 52])));Map.is_bst := 5[47 , 49 , 50 , 52]( 5[8 , 50 , 52]( 4[9 , 47 , 49 , 50]( 3 [48]( 2 [46]( 1[30 , 39 , 41]( 0[31]( [list int))))))))|}, 0, 10]: Map.bst * list int * in*)
 Definition s7 := Eval compute in step_checker s6 (EqTr (t_i:=t_i) t_func  t_atom  t_form  4 8(49%int63 :: 51%int63 :: 47%int63 :: nil)).
Print s7.
(*s7 =({|Map.this :=( 0[31] ) 1[30 , 39 , 41](( 2[46] ) 3[48]( 4[8 , 47 , 49 , 51]( 5[47 , 49 , 50 , 52])));Map.is_bst := 4[8 , 47 , 49 , 51]( 5[47 , 49 , 50 , 52]( 5[8 , 50 , 52]( 4[9 , 47 , 49 , 50]( 3 [48]( 2[46]( 1[30 , 39 , 41]( 0[31]( [list int)))))))))|}, 0, 10]: Map.bst * list int * in*)
 Definition s8 := Eval compute in step_checker s7 (BuildDef (t_i:=t_i) t_func  t_atom  t_form  6 52).
Print s8.
(*s8 =({|Map.this :=(( 0[31] ) 1[30 , 39 , 41]( 2[46] )) 3[48]( 4[8 , 47 , 49 , 51]( 5[47 , 49 , 50 , 52]( 6[9 , 51 , 52])));Map.is_bst := 6 [9 , 51 , 52]( 4[8 , 47 , 49 , 51]( 5[47 , 49 , 50 , 52]( 5[8 , 50 , 52]( 4[9 , 47 , 49 , 50]( 3[48]( 2[46]( 1[30 , 39 , 41]( 0[31]( [list int))))))))))|}, 0, 10]: Map.bst * list int * in*)
 Definition s9 := Eval compute in step_checker s8 (Res (t_i:=t_i) t_func  t_atom  t_form  6((make 2 0%int63 .[ 0 <- 4%int63]) .[ 1 <-6%int63])%array).
Print s9.
(*s9 =({|Map.this :=(( 0[31] ) 1[30 , 39 , 41]( 2[46] )) 3[48]( 4[8 , 47 , 49 , 51]( 5[47 , 49 , 50 , 52]( 6[47 , 49 , 51 , 52])));Map.is_bst := 6[47 , 49 , 51 , 52]( 6[9 , 51 , 52]( 4[8 , 47 , 49 , 51]( 5[47 , 49 , 50 , 52]( 5[8 , 50 , 52]( 4[9 , 47 , 49 , 50]( 3[48]( 2[46]( 1[30 , 39 , 41]( 0[31]( [list int)))))))))))|}, 0, 10]: Map.bst * list int * in*)
 Definition s10 := Eval compute in step_checker s9 (Res (t_i:=t_i) t_func  t_atom  t_form  6((((make 4 0%int63 .[ 0 <- 5%int63]) .[ 1 <-6%int63]) .[ 2 <- 2%int63]) .[ 3 <-3%int63])%array).
Print s10.
(*s10 =({|Map.this :=(( 0[31] ) 1[30 , 39 , 41]( 2[46] )) 3[48]( 4[8 , 47 , 49 , 51]( 5[47 , 49 , 50 , 52]( 6[52] )));Map.is_bst := 6 [52]( 6[47 , 49 , 51 , 52]( 6[9 , 51 , 52]( 4[8 , 47 , 49 , 51]( 5[47 , 49 , 50 , 52]( 5[8 , 50 , 52]( 4[9 , 47 , 49 , 50]( 3[48]( 2[46]( 1[30 , 39 , 41]( 0[31]( [list int))))))))))))|}, 0, 10]: Map.bst * list int * in*)
 Definition s11 := Eval compute in step_checker s10 (LiaMicromega (t_i:=t_i) t_func  t_atom  t_form 5 (54%int63 :: nil)(ZMicromega.RatProof(RingMicromega.PsatzAdd(RingMicromega.PsatzMulE(RingMicromega.PsatzC 2)(RingMicromega.PsatzIn Z 1))(RingMicromega.PsatzIn Z 0))ZMicromega.DoneProof:: ZMicromega.RatProof(RingMicromega.PsatzAdd(RingMicromega.PsatzMulC(EnvRing.Pc (-2))(RingMicromega.PsatzIn Z 1))(RingMicromega.PsatzIn Z 0))ZMicromega.DoneProof:: ZMicromega.RatProof(RingMicromega.PsatzAdd(RingMicromega.PsatzMulC(EnvRing.Pc (-1))(RingMicromega.PsatzIn Z 1))(RingMicromega.PsatzIn Z 0))ZMicromega.DoneProof:: ZMicromega.RatProof(RingMicromega.PsatzAdd(RingMicromega.PsatzIn Z 1)(RingMicromega.PsatzMulE(RingMicromega.PsatzC 2)(RingMicromega.PsatzIn Z 0)))ZMicromega.DoneProof:: ZMicromega.RatProof(RingMicromega.PsatzAdd(RingMicromega.PsatzMulC(EnvRing.Pc (-1))(RingMicromega.PsatzIn Z 1))(RingMicromega.PsatzMulE(RingMicromega.PsatzC 2)(RingMicromega.PsatzIn Z 0)))ZMicromega.DoneProof::ZMicromega.RatProof(RingMicromega.PsatzAdd(RingMicromega.PsatzMulC(EnvRing.Pc (-2))(RingMicromega.PsatzIn Z 1))(RingMicromega.PsatzMulE(RingMicromega.PsatzC 2)(RingMicromega.PsatzIn Z 0)))ZMicromega.DoneProof :: nil)).
Print s11.
(*s11 =({|Map.this :=(( 0[31] ) 1[30 , 39 , 41]( 2[46] )) 3[48]( 4[8 , 47 , 49 , 51]( 5[0]( 6[52] )));Map.is_bst := 5 [0]( 6 [52]( 6[47 , 49 , 51 , 52]( 6[9 , 51 , 52]( 4[8 , 47 , 49 , 51]( 5[47 , 49 , 50 , 52]( 5[8 , 50 , 52]( 4[9, 47 , 49 , 50]( 3[48]( 2[46]( 1[30 , 39 , 41]( 0[31]( [list int)))))))))))))|}, 0, 10]: Map.bst * list int * in*)
 Definition s12 := Eval compute in step_checker s11 (BuildDef (t_i:=t_i) t_func  t_atom  t_form 4 53).
Print s12.
(*s12 =({|Map.this :=(( 0[31] ) 1[30 , 39 , 41]( 2[46] )) 3[48]( 4[8 , 51 , 53]( 5[0]( 6[52] )));Map.is_bst := 4 [8 , 51 , 53]( 5 [0]( 6 [52]( 6[47 , 49 , 51 , 52]( 6[9 , 51 , 52]( 4[8 , 47 , 49 , 51]( 5[47 , 49 , 50 , 52]( 5[8 , 50 , 52]( 4[9, 47 , 49 , 50]( 3[48]( 2[46]( 1[30, 39 , 41]( 0[31]([list int))))))))))))))|}, 0, 10]: Map.bst * list int * in*)
 Definition s13 := Eval compute in step_checker s12 (Res (t_i:=t_i) t_func  t_atom  t_form  4((make 2 0%int63 .[ 0 <- 4%int63]).[ 1 <- 6%int63])%array).
Print s13.
(*s13 =({|Map.this :=(( 0[31] ) 1[30 , 39 , 41]( 2[46] )) 3[48]( 4[8 , 51]( 5[0]( 6[52] )));Map.is_bst := 4 [8 , 51]( 4[8 , 51 , 53]( 5 [0]( 6 [52]( 6[47 , 49 , 51 , 52]( 6[9 , 51 , 52]( 4[8 , 47 , 49 , 51]( 5[47, 49 , 50 , 52]( 5[8 , 50 , 52]( 4[9, 47 , 49 , 50]( 3[48]( 2[46]( 1[30, 39 , 41]( 0[31]([list int)))))))))))))))|}, 0, 10]: Map.bst * list int * in*)
 Definition s14 := Eval compute in step_checker s13 (BuildDef (t_i:=t_i) t_func  t_atom t_form  7 55).
Print s14.
(*s14 =({|Map.this :=(( 0[31] ) 1[30 , 39 , 41]( 2[46] )) 3[48](( 4[8 , 51] )5 [0]( 6[52]( 7[27 , 50 , 55])));Map.is_bst := 7 [27 , 50 , 55]( 4 [8 , 51]( 4[8 , 51 , 53]( 5 [0]( 6 [52]( 6[47 , 49 , 51 , 52]( 6[9 , 51 , 52]( 4[8, 47 , 49 , 51]( 5[47, 49 , 50 , 52]( 5[8 , 50 , 52]( 4[9, 47, 49 , 50]( 3[48]( 2[46]( 1[30,39 , 41]( 0[31]([list int))))))))))))))))|}, 0, 10]: Map.bst * list int * in*)
 Definition s15 := Eval compute in step_checker s14 (Res (t_i:=t_i) t_func  t_atom t_form  7((make 2 0%int63 .[ 0 <-7%int63]) .[ 1 <- 5%int63])%array).
Print s15.
(*s15 =({|Map.this :=(( 0[31] ) 1[30 , 39 , 41]( 2[46] )) 3[48](( 4[8 , 51] )5 [0]( 6[52]( 7[0 , 0] )))4;Map.is_bst := 7 [0 , 0]( 7[27 , 50 , 55]( 4 [8 , 51]( 4[8 , 51 , 53]( 5 [0]( 6[52]( 6[47 , 49 , 51 , 52]( 6[9 , 51 , 52]( 4[8, 47 , 49 , 51]( 5[47, 49 , 50 , 52]( 5[8 , 50 , 52]( 4[9, 47, 49 , 50]( 3[48]( 2[46]( 1[30,39 ,41](0[31]([list int)))))))))))))))))|}, 0, 10]: Map.bst * list int * in*)
(* ====> ":: 0%int63 " in output found, break *)
Definition confl := Eval compute in let (_, _, confl) := trace in confl.
Compute (C.is_false (S.get s15 confl)).