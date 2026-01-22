Add Rec LoadPath "../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool. 
Require Import Int31. 
Local Open Scope int31_scope.

Section test8cvc5debug. 

 Parse_certif_verit t_i t_func t_atom t_form root used_roots trace 
 "test8cvc5/test8cvc5.smt2" 
 "test8cvc5/test8cvc5.pf". 

 Definition nclauses := Eval vm_compute in (match trace with Certif a _ _ => a end). (* Size of the state *)
 Print nclauses.

  Definition c := Eval vm_compute in (match trace with Certif _ a _ => a end). (* Certificate *)
 Definition conf := Eval vm_compute in (match trace with Certif _ _ a => a end). (* Look here in the state for the empty clause*)
 Print conf.

 Eval vm_compute in List.length (fst c). (* No. of steps in certificate *) 
End test8cvc5debug.