Require Import SMTCoq.SMTCoq.

Variables (A B : Type).

Goal forall (f g : A -> list B) (x y : A), (forall a, f a = g a) -> x = y -> f x = f y.
Proof. smt. (* No problems here: A is a separate type, listB is a separate type, and f and g have arrow types. *) admit. admit. Admitted.

Goal forall (f : A -> list B) (fho : (A -> list B) -> list B -> A) (l1 l2 : list B), fho f l1 = fho f l2.
Proof.
  intros. Fail abduce 1. Abort. 

Lemma flat_map_ext : forall (A B : Type)(f g : A -> list B),
  (forall a, f a = g a) -> forall l, flat_map f l = flat_map g l.
Proof.
  intros A B f g Hext l. Fail abduce 1.
  (* Now we have a problem, output:
The command has indeed failed with message:
Solver error: (error argument type is not a subtype of the function's argument type:
argument:  op_1
has type:  (-> Tindex_1 Tindex_0)
not subtype: Tindex_0
in term : (op_3 (as op_1 Tindex_0) op_2) ).
    The problem is that since f is an argument to flat_map, its type is   
    coerced into a single type. The right thing to do here would be to 
    recognize that this is a higher order function application and throw 
    an error saying the solver wouldn't support it *)
Abort.