Require Import SMTCoq.SMTCoq.

Require Export BinNums BinPos Pnat.
Require Import BinNat Bool Equalities GenericMinMax
 OrdersFacts ZAxioms ZProperties DecidableClass.
Require BinIntDef.

(***********************************************************)
(** * Binary Integers *)
(***********************************************************)

(** Initial author: Pierre Crégut, CNET, Lannion, France *)

(** The type [Z] and its constructors [Z0] and [Zpos] and [Zneg]
    are now defined in [BinNums.v] *)

Local Open Scope Z_scope.

(** Every definitions and early properties about binary integers
    are placed in a module [Z] for qualification purpose. *)

Module Z
 <: ZAxiomsSig
 <: UsualOrderedTypeFull
 <: UsualDecidableTypeFull
 <: TotalOrder.

(** * Definitions of operations, now in a separate file *)

Include BinIntDef.Z.

Register add as num.Z.add.
Register opp as num.Z.opp.
Register succ as num.Z.succ.
Register pred as num.Z.pred.
Register sub as num.Z.sub.
Register mul as num.Z.mul.
Register pow as num.Z.pow.
Register of_nat as num.Z.of_nat.



(** When including property functors, only inline t eq zero one two *)

Set Inline Level 30.

(** * Logic Predicates *)

Definition eq := @Logic.eq Z.
Definition eq_equiv := @eq_equivalence Z.

Definition lt x y := (x ?= y) = Lt.
Definition gt x y := (x ?= y) = Gt.
Definition le x y := (x ?= y) <> Gt.
Definition ge x y := (x ?= y) <> Lt.

Infix "<=" := le : Z_scope.
Infix "<" := lt : Z_scope.
Infix ">=" := ge : Z_scope.
Infix ">" := gt : Z_scope.

Notation "x <= y <= z" := (x <= y /\ y <= z) : Z_scope.
Notation "x <= y < z" := (x <= y /\ y < z) : Z_scope.
Notation "x < y < z" := (x < y /\ y < z) : Z_scope.
Notation "x < y <= z" := (x < y /\ y <= z) : Z_scope.

Definition divide x y := exists z, y = z*x.
Notation "( x | y )" := (divide x y) (at level 0).

Definition Even a := exists b, a = 2*b.
Definition Odd a := exists b, a = 2*b+1.

Register le as num.Z.le.
Register lt as num.Z.lt.
Register ge as num.Z.ge.
Register gt as num.Z.gt.
Register leb as num.Z.leb.
Register ltb as num.Z.ltb.
Register geb as num.Z.geb.
Register gtb as num.Z.gtb.
Register eqb as num.Z.eqb.

(** * Decidability of equality. *)

Definition eq_dec (x y : Z) : {x = y} + {x <> y}.
Proof. Show. Fail (abduce 3). Admitted.

(** *  of morphisms, obvious since eq is Leibniz *)

Local Obligation Tactic := simpl_relation.
Program Definition succ_wd : Proper (eq==>eq) succ := _.
Program Definition pred_wd : Proper (eq==>eq) pred := _.
Program Definition opp_wd : Proper (eq==>eq) opp := _.
Program Definition add_wd : Proper (eq==>eq==>eq) add := _.
Program Definition sub_wd : Proper (eq==>eq==>eq) sub := _.
Program Definition mul_wd : Proper (eq==>eq==>eq) mul := _.
Program Definition lt_wd : Proper (eq==>eq==>iff) lt := _.
Program Definition div_wd : Proper (eq==>eq==>eq) div := _.
Program Definition mod_wd : Proper (eq==>eq==>eq) modulo := _.
Program Definition quot_wd : Proper (eq==>eq==>eq) quot := _.
Program Definition rem_wd : Proper (eq==>eq==>eq) rem := _.
Program Definition pow_wd : Proper (eq==>eq==>eq) pow := _.
Program Definition testbit_wd : Proper (eq==>eq==>Logic.eq) testbit := _.

(** * Properties of [pos_sub] *)

(** [pos_sub] can be written in term of positive comparison
    and subtraction (cf. earlier definition of addition of Z) *)

Lemma pos_sub_spec p q :
 pos_sub p q =
 match (p ?= q)%positive with
   | Eq => 0
   | Lt => neg (q - p)
   | Gt => pos (p - q)
 end.
Proof. Show. Fail (abduce 3). Admitted.

Lemma pos_sub_discr p q :
  match pos_sub p q with
  | Z0 => p = q
  | pos k => p = q + k
  | neg k => q = p + k
  end%positive.
Proof. Show. Fail (abduce 3). Admitted.

(** Particular cases of the previous result *)

Lemma pos_sub_diag p : pos_sub p p = 0.
Proof. Show. Fail (abduce 3). Admitted.

Lemma pos_sub_lt p q : (p < q)%positive -> pos_sub p q = neg (q - p).
Proof. Show. Fail (abduce 3). Admitted.

Lemma pos_sub_gt p q : (q < p)%positive -> pos_sub p q = pos (p - q).
Proof. Show. Fail (abduce 3). Admitted.

(** The opposite of [pos_sub] is [pos_sub] with reversed arguments *)

Lemma pos_sub_opp p q : - pos_sub p q = pos_sub q p.
Proof. Show. Fail (abduce 3). Admitted.

(** In the following module, we group results that are needed now
  to prove specifications of operations, but will also be provided
  later by the generic functor of properties. *)

Module Import Private_BootStrap.

(** ** Operations and constants *)

Lemma add_0_r n : n + 0 = n.
Proof. Show. Fail (abduce 3). Admitted.

Lemma mul_0_r n : n * 0 = 0.
Proof. Show. Fail (abduce 3). Admitted.

Lemma mul_1_l n : 1 * n = n.
Proof. Show. Fail (abduce 3). Admitted.

(** ** Addition is commutative *)

Lemma add_comm n m : n + m = m + n.
Proof. Show. Fail (abduce 3). Admitted.

(** ** Opposite distributes over addition *)

Lemma opp_add_distr n m : - (n + m) = - n + - m.
Proof. Show. Fail (abduce 3). Admitted.

(** ** Opposite is injective *)

Lemma opp_inj n m : -n = -m -> n = m.
Proof. Show. Fail (abduce 3). Admitted.

(** ** Addition is associative *)

Lemma pos_sub_add p q r :
  pos_sub (p + q) r = pos p + pos_sub q r.
Proof. Show. Fail (abduce 3). Admitted.

Local Arguments add !x !y.

Lemma add_assoc_pos p n m : pos p + (n + m) = pos p + n + m.
Proof. Show. Fail (abduce 3). Admitted.

Lemma add_assoc n m p : n + (m + p) = n + m + p.
Proof. Show. Fail (abduce 3). Admitted.

(** ** Opposite is inverse for addition *)

Lemma add_opp_diag_r n : n + - n = 0.
Proof. Show. Fail (abduce 3). Admitted.

(** ** Multiplication and Opposite *)

Lemma mul_opp_r n m : n * - m = - (n * m).
Proof. Show. Fail (abduce 3). Admitted.

(** ** Distributivity of multiplication over addition *)

Lemma mul_add_distr_pos (p:positive) n m :
 (n + m) * pos p = n * pos p + m * pos p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma mul_add_distr_r n m p : (n + m) * p = n * p + m * p.
Proof. Show. Fail (abduce 3). Admitted.

End Private_BootStrap.

(** *  of specifications *)

(** ** Specification of constants *)

Lemma one_succ : 1 = succ 0.
Proof. Show. Fail (abduce 3). Admitted.

Lemma two_succ : 2 = succ 1.
Proof. Show. Fail (abduce 3). Admitted.

(** ** Specification of addition *)

Lemma add_0_l n : 0 + n = n.
Proof. Show. Fail (abduce 3). Admitted.

Lemma add_succ_l n m : succ n + m = succ (n + m).
Proof. Show. Fail (abduce 3). Admitted.

(** ** Specification of opposite *)

Lemma opp_0 : -0 = 0.
Proof. Show. Fail (abduce 3). Admitted.

Lemma opp_succ n : -(succ n) = pred (-n).
Proof. Show. Fail (abduce 3). Admitted.

(** ** Specification of successor and predecessor *)

Local Arguments pos_sub : simpl nomatch.

Lemma succ_pred n : succ (pred n) = n.
Proof. Show. Fail (abduce 3). Admitted.

Lemma pred_succ n : pred (succ n) = n.
Proof. Show. Fail (abduce 3). Admitted.

(** ** Specification of subtraction *)

Lemma sub_0_r n : n - 0 = n.
Proof. Show. Fail (abduce 3). Admitted.

Lemma sub_succ_r n m : n - succ m = pred (n - m).
Proof. Show. Fail (abduce 3). Admitted.

(** ** Specification of multiplication *)

Lemma mul_0_l n : 0 * n = 0.
Proof. Show. Fail (abduce 3). Admitted.

Lemma mul_succ_l n m : succ n * m = n * m + m.
Proof. Show. Fail (abduce 3). Admitted.

(** ** Specification of comparisons and order *)

Lemma eqb_eq n m : (n =? m) = true <-> n = m.
Proof. Show. Fail (abduce 3). Admitted.

#[global]
Instance Decidable_eq_Z : forall (x y : Z), Decidable (eq x y) := {
  Decidable_spec := Z.eqb_eq x y
}.

Lemma ltb_lt n m : (n <? m) = true <-> n < m.
Proof. Show. Fail (abduce 3). Admitted.

#[global]
Instance Decidable_lt_Z : forall (x y : Z), DecidableClass.Decidable (x < y)%Z := {
  Decidable_spec := Z.ltb_lt x y
}.

Lemma leb_le n m : (n <=? m) = true <-> n <= m.
Proof. Show. Fail (abduce 3). Admitted.

#[global]
Instance Decidable_le_Z : forall (x y : Z), DecidableClass.Decidable (x <= y)%Z := {
  Decidable_spec := Z.leb_le x y
}.

Lemma gtb_gt n m : (n >? m) = true <-> n > m.
Proof. Show. Fail (abduce 3). Admitted.

#[global]
Instance Decidable_gt_Z : forall (x y : Z), DecidableClass.Decidable (x > y)%Z := {
  Decidable_spec := Z.gtb_gt x y
}.

Lemma geb_ge n m : (n >=? m) = true <-> n >= m.
Proof. Show. Fail (abduce 3). Admitted.

#[global]
Instance Decidable_ge_Z : forall (x y : Z), DecidableClass.Decidable (x >= y)%Z := {
  Decidable_spec := Z.geb_ge x y
}.

Lemma compare_eq_iff n m : (n ?= m) = Eq <-> n = m.
Proof. Show. Fail (abduce 3). Admitted.

Lemma compare_sub n m : (n ?= m) = (n - m ?= 0).
Proof. Show. Fail (abduce 3). Admitted.

Lemma compare_antisym n m : (m ?= n) = CompOpp (n ?= m).
Proof. Show. Fail (abduce 3). Admitted.

Lemma compare_lt_iff n m : (n ?= m) = Lt <-> n < m.
Proof. Show. Fail (abduce 3). Admitted.

Lemma compare_le_iff n m : (n ?= m) <> Gt <-> n <= m.
Proof. Show. Fail (abduce 3). Admitted.

(** Some more advanced properties of comparison and orders,
    including [compare_spec] and [lt_irrefl] and [lt_eq_cases]. *)

Include BoolOrderFacts.

(** Remaining specification of [lt] and [le] *)

Lemma lt_succ_r n m : n < succ m <-> n<=m.
Proof. Show. Fail (abduce 3). Admitted.

(** ** Specification of minimum and maximum *)

Lemma max_l n m : m<=n -> max n m = n.
Proof. Show. Fail (abduce 3). Admitted.

Lemma max_r n m :  n<=m -> max n m = m.
Proof. Show. Fail (abduce 3). Admitted.

Lemma min_l n m : n<=m -> min n m = n.
Proof. Show. Fail (abduce 3). Admitted.

Lemma min_r n m : m<=n -> min n m = m.
Proof. Show. Fail (abduce 3). Admitted.

(** ** Induction principles based on successor / predecessor *)

Lemma peano_ind (P : Z -> Prop) :
  P 0 ->
  (forall x, P x -> P (succ x)) ->
  (forall x, P x -> P (pred x)) ->
  forall z, P z.
Proof. Show. Fail (abduce 3). Admitted.

Lemma bi_induction (P : Z -> Prop) :
  Proper (eq ==> iff) P ->
  P 0 ->
  (forall x, P x <-> P (succ x)) ->
  forall z, P z.
Proof. Show. Fail (abduce 3). Admitted.

(** We can now derive all properties of basic functions and orders,
    and use these properties for proving the specs of more advanced
    functions. *)

Include ZBasicProp <+ UsualMinMaxLogicalProperties <+ UsualMinMaxDecProperties.

Register eq_decidable as num.Z.eq_decidable.
Register le_decidable as num.Z.le_decidable.
Register lt_decidable as num.Z.lt_decidable.


(** ** Specification of absolute value *)

Lemma abs_eq n : 0 <= n -> abs n = n.
Proof. Show. Fail (abduce 3). Admitted.

Lemma abs_neq n : n <= 0 -> abs n = - n.
Proof. Show. Fail (abduce 3). Admitted.

(** ** Specification of sign *)

Lemma sgn_null n : n = 0 -> sgn n = 0.
Proof. Show. Fail (abduce 3). Admitted.

Lemma sgn_pos n : 0 < n -> sgn n = 1.
Proof. Show. Fail (abduce 3). Admitted.

Lemma sgn_neg n : n < 0 -> sgn n = -1.
Proof. Show. Fail (abduce 3). Admitted.

(** ** Specification of power *)

Lemma pow_0_r n : n^0 = 1.
Proof. Show. Fail (abduce 3). Admitted.

Lemma pow_succ_r n m : 0<=m -> n^(succ m) = n * n^m.
Proof. Show. Fail (abduce 3). Admitted.

Lemma pow_neg_r n m : m<0 -> n^m = 0.
Proof. Show. Fail (abduce 3). Admitted.

(** For folding back a [pow_pos] into a [pow] *)

Lemma pow_pos_fold n p : pow_pos n p = n ^ (pos p).
Proof. Show. Fail (abduce 3). Admitted.

(** ** Specification of square *)

Lemma square_spec n : square n = n * n.
Proof. Show. Fail (abduce 3). Admitted.

(** ** Specification of square root *)

Lemma sqrtrem_spec n : 0<=n ->
 let (s,r) := sqrtrem n in n = s*s + r /\ 0 <= r <= 2*s.
Proof. Show. Fail (abduce 3). Admitted.

Lemma sqrt_spec n : 0<=n ->
 let s := sqrt n in s*s <= n < (succ s)*(succ s).
Proof. Show. Fail (abduce 3). Admitted.

Lemma sqrt_neg n : n<0 -> sqrt n = 0.
Proof. Show. Fail (abduce 3). Admitted.

Lemma sqrtrem_sqrt n : fst (sqrtrem n) = sqrt n.
Proof. Show. Fail (abduce 3). Admitted.

(** ** Specification of logarithm *)

Lemma log2_spec n : 0 < n -> 2^(log2 n) <= n < 2^(succ (log2 n)).
Proof. Show. Fail (abduce 3). Admitted.

Lemma log2_nonpos n : n<=0 -> log2 n = 0.
Proof. Show. Fail (abduce 3). Admitted.

(** Specification of parity functions *)

Lemma even_spec n : even n = true <-> Even n.
Proof. Show. Fail (abduce 3). Admitted.

Lemma odd_spec n : odd n = true <-> Odd n.
Proof. Show. Fail (abduce 3). Admitted.

(** ** Multiplication and Doubling *)

Lemma double_spec n : double n = 2*n.
Proof. Show. Fail (abduce 3). Admitted.

Lemma succ_double_spec n : succ_double n = 2*n + 1.
Proof. Show. Fail (abduce 3). Admitted.

Lemma pred_double_spec n : pred_double n = 2*n - 1.
Proof. Show. Fail (abduce 3). Admitted.

(** ** Correctness  for Trunc division *)

Lemma pos_div_eucl_eq a b : 0 < b ->
  let (q, r) := pos_div_eucl a b in pos a = q * b + r.
Proof. Show. Fail (abduce 3). Admitted.

Lemma div_eucl_eq a b : b<>0 ->
 let (q, r) := div_eucl a b in a = b * q + r.
Proof. Show. Fail (abduce 3). Admitted.

Lemma div_mod a b : b<>0 -> a = b*(a/b) + (a mod b).
Proof. Show. Fail (abduce 3). Admitted.

Lemma pos_div_eucl_bound a b : 0<b -> 0 <= snd (pos_div_eucl a b) < b.
Proof. Show. Fail (abduce 3). Admitted.

Lemma mod_pos_bound a b : 0 < b -> 0 <= a mod b < b.
Proof. Show. Fail (abduce 3). Admitted.

Definition mod_bound_pos a b (_:0<=a) := mod_pos_bound a b.

Lemma mod_neg_bound a b : b < 0 -> b < a mod b <= 0.
Proof. Show. Fail (abduce 3). Admitted.

(** ** Correctness  for Floor division *)

Theorem quotrem_eq a b : let (q,r) := quotrem a b in a = q * b + r.
Proof. Show. Fail (abduce 3). Admitted.

Lemma quot_rem' a b : a = b*(a÷b) + rem a b.
Proof. Show. Fail (abduce 3). Admitted.

Lemma quot_rem a b : b<>0 -> a = b*(a÷b) + rem a b.
Proof. Show. Fail (abduce 3). Admitted.

Lemma rem_bound_pos a b : 0<=a -> 0<b -> 0 <= rem a b < b.
Proof. Show. Fail (abduce 3). Admitted.

Lemma rem_opp_l' a b : rem (-a) b = - (rem a b).
Proof. Show. Fail (abduce 3). Admitted.

Lemma rem_opp_r' a b : rem a (-b) = rem a b.
Proof. Show. Fail (abduce 3). Admitted.

Lemma rem_opp_l a b : b<>0 -> rem (-a) b = - (rem a b).
Proof. Show. Fail (abduce 3). Admitted.

Lemma rem_opp_r a b : b<>0 -> rem a (-b) = rem a b.
Proof. Show. Fail (abduce 3). Admitted.

(** ** Extra properties about [divide] *)

Lemma divide_Zpos p q : (pos p|pos q) <-> (p|q)%positive.
Proof. Show. Fail (abduce 3). Admitted.

Lemma divide_Zpos_Zneg_r n p : (n|pos p) <-> (n|neg p).
Proof. Show. Fail (abduce 3). Admitted.

Lemma divide_Zpos_Zneg_l n p : (pos p|n) <-> (neg p|n).
Proof. Show. Fail (abduce 3). Admitted.

(** ** Correctness  for gcd *)

Lemma ggcd_gcd a b : fst (ggcd a b) = gcd a b.
Proof. Show. Fail (abduce 3). Admitted.

Lemma ggcd_correct_divisors a b :
  let '(g,(aa,bb)) := ggcd a b in
  a = g*aa /\ b = g*bb.
Proof. Show. Fail (abduce 3). Admitted.

Lemma gcd_divide_l a b : (gcd a b | a).
Proof. Show. Fail (abduce 3). Admitted.

Lemma gcd_divide_r a b : (gcd a b | b).
Proof. Show. Fail (abduce 3). Admitted.

Lemma gcd_greatest a b c : (c|a) -> (c|b) -> (c | gcd a b).
Proof. Show. Fail (abduce 3). Admitted.

Lemma gcd_nonneg a b : 0 <= gcd a b.
Proof. Show. Fail (abduce 3). Admitted.

(** ggcd and opp : an auxiliary result used in QArith *)

Theorem ggcd_opp a b :
  ggcd (-a) b = (let '(g,(aa,bb)) := ggcd a b in (g,(-aa,bb))).
Proof. Show. Fail (abduce 3). Admitted.

(** ** Extra properties about [testbit] *)

Lemma testbit_of_N a n :
 testbit (of_N a) (of_N n) = N.testbit a n.
Proof. Show. Fail (abduce 3). Admitted.

Lemma testbit_of_N' a n : 0<=n ->
 testbit (of_N a) n = N.testbit a (to_N n).
Proof. Show. Fail (abduce 3). Admitted.

Lemma testbit_Zpos a n : 0<=n ->
 testbit (pos a) n = N.testbit (N.pos a) (to_N n).
Proof. Show. Fail (abduce 3). Admitted.

Lemma testbit_Zneg a n : 0<=n ->
 testbit (neg a) n = negb (N.testbit (Pos.pred_N a) (to_N n)).
Proof. Show. Fail (abduce 3). Admitted.

(** **  of specifications for bitwise operations *)

Lemma div2_spec a : div2 a = shiftr a 1.
Proof. Show. Fail (abduce 3). Admitted.

Lemma testbit_0_l n : testbit 0 n = false.
Proof. Show. Fail (abduce 3). Admitted.

Lemma testbit_neg_r a n : n<0 -> testbit a n = false.
Proof. Show. Fail (abduce 3). Admitted.

Lemma testbit_odd_0 a : testbit (2*a+1) 0 = true.
Proof. Show. Fail (abduce 3). Admitted.

Lemma testbit_even_0 a : testbit (2*a) 0 = false.
Proof. Show. Fail (abduce 3). Admitted.

Lemma testbit_odd_succ a n : 0<=n ->
 testbit (2*a+1) (succ n) = testbit a n.
Proof. Show. Fail (abduce 3). Admitted.

Lemma testbit_even_succ a n : 0<=n ->
 testbit (2*a) (succ n) = testbit a n.
Proof. Show. Fail (abduce 3). Admitted.

(** Correctness  about [Z.shiftr] and [Z.shiftl] *)

Lemma shiftr_spec_aux a n m : 0<=n -> 0<=m ->
                              testbit (shiftr a n) m = testbit a (m+n).
Proof. Show. Fail (abduce 3). Admitted.

Lemma shiftl_spec_low a n m : m<n ->
                              testbit (shiftl a n) m = false.
Proof. Show. Fail (abduce 3). Admitted.

Lemma shiftl_spec_high a n m : 0<=m -> n<=m ->
                               testbit (shiftl a n) m = testbit a (m-n).
Proof. Show. Fail (abduce 3). Admitted.

Lemma shiftr_spec a n m : 0<=m ->
 testbit (shiftr a n) m = testbit a (m+n).
Proof. Show. Fail (abduce 3). Admitted.

(** Correctness  for bitwise operations *)

Lemma lor_spec a b n :
 testbit (lor a b) n = testbit a n || testbit b n.
Proof. Show. Fail (abduce 3). Admitted.

Lemma land_spec a b n :
 testbit (land a b) n = testbit a n && testbit b n.
Proof. Show. Fail (abduce 3). Admitted.

Lemma ldiff_spec a b n :
 testbit (ldiff a b) n = testbit a n && negb (testbit b n).
Proof. Show. Fail (abduce 3). Admitted.

Lemma lxor_spec a b n :
 testbit (lxor a b) n = xorb (testbit a n) (testbit b n).
Proof. Show. Fail (abduce 3). Admitted.


(** Generic properties of advanced functions. *)

Include ZExtraProp.

Theorem mod_bound_pos_le a b : 0 <= a -> 0 < b -> 0 <= a mod b <= a.
Proof. Show. Fail (abduce 3). Admitted.

(** In generic statements, the predicates [lt] and [le] have been
  favored, whereas [gt] and [ge] don't even exist in the abstract
  layers. The use of [gt] and [ge] is hence not recommended. We provide
  here the bare minimal results to related them with [lt] and [le]. *)

Lemma gt_lt_iff n m : n > m <-> m < n.
Proof. Show. Fail (abduce 3). Admitted.

Lemma gt_lt n m : n > m -> m < n.
Proof. Show. Fail (abduce 3). Admitted.

Lemma lt_gt n m : n < m -> m > n.
Proof. Show. Fail (abduce 3). Admitted.

Lemma ge_le_iff n m : n >= m <-> m <= n.
Proof. Show. Fail (abduce 3). Admitted.

Lemma ge_le n m : n >= m -> m <= n.
Proof. Show. Fail (abduce 3). Admitted.

Lemma le_ge n m : n <= m -> m >= n.
Proof. Show. Fail (abduce 3). Admitted.

(** We provide a tactic converting from one style to the other. *)

Ltac swap_greater := rewrite ?gt_lt_iff in *; rewrite ?ge_le_iff in *.

(** Similarly, the boolean comparisons [ltb] and [leb] are favored
  over their dual [gtb] and [geb]. We prove here the equivalence
  and a few minimal results. *)

Lemma gtb_ltb n m : (n >? m) = (m <? n).
Proof. Show. Fail (abduce 3). Admitted.

Lemma geb_leb n m : (n >=? m) = (m <=? n).
Proof. Show. Fail (abduce 3). Admitted.

Lemma gtb_lt n m : (n >? m) = true <-> m < n.
Proof. Show. Fail (abduce 3). Admitted.

Lemma geb_le n m : (n >=? m) = true <-> m <= n.
Proof. Show. Fail (abduce 3). Admitted.

Lemma gtb_spec n m : BoolSpec (m<n) (n<=m) (n >? m).
Proof. Show. Fail (abduce 3). Admitted.

Lemma geb_spec n m : BoolSpec (m<=n) (n<m) (n >=? m).
Proof. Show. Fail (abduce 3). Admitted.

(** TODO : to add in Numbers ? *)

Lemma add_reg_l n m p : n + m = n + p -> m = p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma mul_reg_l n m p : p <> 0 -> p * n = p * m -> n = m.
Proof. Show. Fail (abduce 3). Admitted.

Lemma mul_reg_r n m p : p <> 0 -> n * p = m * p -> n = m.
Proof. Show. Fail (abduce 3). Admitted.

Lemma opp_eq_mul_m1 n : - n = n * -1.
Proof. Show. Fail (abduce 3). Admitted.

Lemma add_diag n : n + n = 2 * n.
Proof. Show. Fail (abduce 3). Admitted.

(** * Comparison and opposite *)

Lemma compare_opp n m : (- n ?= - m) = (m ?= n).
Proof. Show. Fail (abduce 3). Admitted.

(** * Comparison and addition *)

Lemma add_compare_mono_l n m p : (n + m ?= n + p) = (m ?= p).
Proof. Show. Fail (abduce 3). Admitted.

(** * [testbit] in terms of comparison. *)

Lemma testbit_mod_pow2 a n i (H : 0 <= n)
  : testbit (a mod 2 ^ n) i = ((i <? n) && testbit a i)%bool.
Proof. Show. Fail (abduce 3). Admitted.

Lemma testbit_ones n i (H : 0 <= n)
  : testbit (ones n) i = ((0 <=? i) && (i <? n))%bool.
Proof. Show. Fail (abduce 3). Admitted.

Lemma testbit_ones_nonneg n i (Hn : 0 <= n) (Hi: 0 <= i)
  : testbit (ones n) i = (i <? n).
Proof. Show. Fail (abduce 3). Admitted.

End Z.

Bind Scope Z_scope with Z.t Z.

(** Re-export Notations *)

Number Notation Z Z.of_num_int Z.to_num_int : Z_scope.

Infix "+" := Z.add : Z_scope.
Notation "- x" := (Z.opp x) : Z_scope.
Infix "-" := Z.sub : Z_scope.
Infix "*" := Z.mul : Z_scope.
Infix "^" := Z.pow : Z_scope.
Infix "/" := Z.div : Z_scope.
Infix "mod" := Z.modulo (at level 40, no associativity) : Z_scope.
Infix "÷" := Z.quot (at level 40, left associativity) : Z_scope.
Infix "?=" := Z.compare (at level 70, no associativity) : Z_scope.
Infix "=?" := Z.eqb (at level 70, no associativity) : Z_scope.
Infix "<=?" := Z.leb (at level 70, no associativity) : Z_scope.
Infix "<?" := Z.ltb (at level 70, no associativity) : Z_scope.
Infix ">=?" := Z.geb (at level 70, no associativity) : Z_scope.
Infix ">?" := Z.gtb (at level 70, no associativity) : Z_scope.
Notation "( x | y )" := (Z.divide x y) (at level 0) : Z_scope.
Infix "<=" := Z.le : Z_scope.
Infix "<" := Z.lt : Z_scope.
Infix ">=" := Z.ge : Z_scope.
Infix ">" := Z.gt : Z_scope.
Notation "x <= y <= z" := (x <= y /\ y <= z) : Z_scope.
Notation "x <= y < z" := (x <= y /\ y < z) : Z_scope.
Notation "x < y < z" := (x < y /\ y < z) : Z_scope.
Notation "x < y <= z" := (x < y /\ y <= z) : Z_scope.

(** Conversions from / to positive numbers *)

Module Pos2Z.

Lemma id p : Z.to_pos (Z.pos p) = p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma inj p q : Z.pos p = Z.pos q -> p = q.
Proof. Show. Fail (abduce 3). Admitted.

Lemma inj_iff p q : Z.pos p = Z.pos q <-> p = q.
Proof. Show. Fail (abduce 3). Admitted.

Lemma is_pos p : 0 < Z.pos p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma is_nonneg p : 0 <= Z.pos p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma inj_1 : Z.pos 1 = 1.
Proof. Show. Fail (abduce 3). Admitted.

Lemma inj_xO p : Z.pos p~0 = 2 * Z.pos p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma inj_xI p : Z.pos p~1 = 2 * Z.pos p + 1.
Proof. Show. Fail (abduce 3). Admitted.

Lemma inj_succ p : Z.pos (Pos.succ p) = Z.succ (Z.pos p).
Proof. Show. Fail (abduce 3). Admitted.

Lemma inj_add p q : Z.pos (p+q) = Z.pos p + Z.pos q.
Proof. Show. Fail (abduce 3). Admitted.

Lemma inj_sub p q : (p < q)%positive ->
 Z.pos (q-p) = Z.pos q - Z.pos p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma inj_sub_max p q : Z.pos (p - q) = Z.max 1 (Z.pos p - Z.pos q).
Proof. Show. Fail (abduce 3). Admitted.

Lemma inj_pred p : p <> 1%positive ->
 Z.pos (Pos.pred p) = Z.pred (Z.pos p).
Proof. Show. Fail (abduce 3). Admitted.

Lemma inj_mul p q : Z.pos (p*q) = Z.pos p * Z.pos q.
Proof. Show. Fail (abduce 3). Admitted.

Lemma inj_pow_pos p q : Z.pos (p^q) = Z.pow_pos (Z.pos p) q.
Proof. Show. Fail (abduce 3). Admitted.

Lemma inj_pow p q : Z.pos (p^q) = (Z.pos p)^(Z.pos q).
Proof. Show. Fail (abduce 3). Admitted.

Lemma inj_square p : Z.pos (Pos.square p) = Z.square (Z.pos p).
Proof. Show. Fail (abduce 3). Admitted.

Lemma inj_compare p q : (p ?= q)%positive = (Z.pos p ?= Z.pos q).
Proof. Show. Fail (abduce 3). Admitted.

Lemma inj_leb p q : (p <=? q)%positive = (Z.pos p <=? Z.pos q).
Proof. Show. Fail (abduce 3). Admitted.

Lemma inj_ltb p q : (p <? q)%positive = (Z.pos p <? Z.pos q).
Proof. Show. Fail (abduce 3). Admitted.

Lemma inj_eqb p q : (p =? q)%positive = (Z.pos p =? Z.pos q).
Proof. Show. Fail (abduce 3). Admitted.

Lemma inj_max p q : Z.pos (Pos.max p q) = Z.max (Z.pos p) (Z.pos q).
Proof. Show. Fail (abduce 3). Admitted.

Lemma inj_min p q : Z.pos (Pos.min p q) = Z.min (Z.pos p) (Z.pos q).
Proof. Show. Fail (abduce 3). Admitted.

Lemma inj_sqrt p : Z.pos (Pos.sqrt p) = Z.sqrt (Z.pos p).
Proof. Show. Fail (abduce 3). Admitted.

Lemma inj_gcd p q : Z.pos (Pos.gcd p q) = Z.gcd (Z.pos p) (Z.pos q).
Proof. Show. Fail (abduce 3). Admitted.

Definition inj_divide p q : (Z.pos p|Z.pos q) <-> (p|q)%positive.
Proof. Show. Fail (abduce 3). Admitted.

Lemma inj_testbit a n : 0<=n ->
 Z.testbit (Z.pos a) n = N.testbit (N.pos a) (Z.to_N n).
Proof. Show. Fail (abduce 3). Admitted.

(** Some results concerning Z.neg and Z.pos *)

Lemma inj_neg p q : Z.neg p = Z.neg q -> p = q.
Proof. Show. Fail (abduce 3). Admitted.

Lemma inj_neg_iff p q : Z.neg p = Z.neg q <-> p = q.
Proof. Show. Fail (abduce 3). Admitted.

Lemma inj_pos p q : Z.pos p = Z.pos q -> p = q.
Proof. Show. Fail (abduce 3). Admitted.

Lemma inj_pos_iff p q : Z.pos p = Z.pos q <-> p = q.
Proof. Show. Fail (abduce 3). Admitted.

Lemma neg_is_neg p : Z.neg p < 0.
Proof. Show. Fail (abduce 3). Admitted.

Lemma neg_is_nonpos p : Z.neg p <= 0.
Proof. Show. Fail (abduce 3). Admitted.

Lemma pos_is_pos p : 0 < Z.pos p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma pos_is_nonneg p : 0 <= Z.pos p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma neg_le_pos p q : Zneg p <= Zpos q.
Proof. Show. Fail (abduce 3). Admitted.

Lemma neg_lt_pos p q : Zneg p < Zpos q.
Proof. Show. Fail (abduce 3). Admitted.

Lemma neg_le_neg p q : (q <= p)%positive -> Zneg p <= Zneg q.
Proof. Show. Fail (abduce 3). Admitted.

Lemma neg_lt_neg p q : (q < p)%positive -> Zneg p < Zneg q.
Proof. Show. Fail (abduce 3). Admitted.

Lemma pos_le_pos p q : (p <= q)%positive -> Zpos p <= Zpos q.
Proof. Show. Fail (abduce 3). Admitted.

Lemma pos_lt_pos p q : (p < q)%positive -> Zpos p < Zpos q.
Proof. Show. Fail (abduce 3). Admitted.

Lemma neg_xO p : Z.neg p~0 = 2 * Z.neg p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma neg_xI p : Z.neg p~1 = 2 * Z.neg p - 1.
Proof. Show. Fail (abduce 3). Admitted.

Lemma pos_xO p : Z.pos p~0 = 2 * Z.pos p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma pos_xI p : Z.pos p~1 = 2 * Z.pos p + 1.
Proof. Show. Fail (abduce 3). Admitted.

Lemma opp_neg p : - Z.neg p = Z.pos p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma opp_pos p : - Z.pos p = Z.neg p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma add_neg_neg p q : Z.neg p + Z.neg q = Z.neg (p+q).
Proof. Show. Fail (abduce 3). Admitted.

Lemma add_pos_neg p q : Z.pos p + Z.neg q = Z.pos_sub p q.
Proof. Show. Fail (abduce 3). Admitted.

Lemma add_neg_pos p q : Z.neg p + Z.pos q = Z.pos_sub q p.
Proof. Show. Fail (abduce 3). Admitted.

Lemma add_pos_pos p q : Z.pos p + Z.pos q = Z.pos (p+q).
Proof. Show. Fail (abduce 3). Admitted.

Lemma divide_pos_neg_r n p : (n|Z.pos p) <-> (n|Z.neg p).
Proof. Show. Fail (abduce 3). Admitted.

Lemma divide_pos_neg_l n p : (Z.pos p|n) <-> (Z.neg p|n).
Proof. Show. Fail (abduce 3). Admitted.

Lemma testbit_neg a n : 0<=n ->
 Z.testbit (Z.neg a) n = negb (N.testbit (Pos.pred_N a) (Z.to_N n)).
Proof. Show. Fail (abduce 3). Admitted.

Lemma testbit_pos a n : 0<=n ->
 Z.testbit (Z.pos a) n = N.testbit (N.pos a) (Z.to_N n).
Proof. Show. Fail (abduce 3). Admitted.

End Pos2Z.

Module Z2Pos.

Lemma id x : 0 < x -> Z.pos (Z.to_pos x) = x.
Proof. Show. Fail (abduce 3). Admitted.

Lemma inj x y : 0 < x -> 0 < y -> Z.to_pos x = Z.to_pos y -> x = y.
Proof. Show. Fail (abduce 3). Admitted.

Lemma inj_iff x y : 0 < x -> 0 < y -> (Z.to_pos x = Z.to_pos y <-> x = y).
Proof. Show. Fail (abduce 3). Admitted.

Lemma to_pos_nonpos x : x <= 0 -> Z.to_pos x = 1%positive.
Proof. Show. Fail (abduce 3). Admitted.

Lemma inj_1 : Z.to_pos 1 = 1%positive.
Proof. Show. Fail (abduce 3). Admitted.

Lemma inj_double x : 0 < x ->
 Z.to_pos (Z.double x) = (Z.to_pos x)~0%positive.
Proof. Show. Fail (abduce 3). Admitted.

Lemma inj_succ_double x : 0 < x ->
 Z.to_pos (Z.succ_double x) = (Z.to_pos x)~1%positive.
Proof. Show. Fail (abduce 3). Admitted.

Lemma inj_succ x : 0 < x -> Z.to_pos (Z.succ x) = Pos.succ (Z.to_pos x).
Proof. Show. Fail (abduce 3). Admitted.

Lemma inj_add x y : 0 < x -> 0 < y ->
 Z.to_pos (x+y) = (Z.to_pos x + Z.to_pos y)%positive.
Proof. Show. Fail (abduce 3). Admitted.

Lemma inj_sub x y : 0 < x < y ->
 Z.to_pos (y-x) = (Z.to_pos y - Z.to_pos x)%positive.
Proof. Show. Fail (abduce 3). Admitted.

Lemma inj_pred x : 1 < x -> Z.to_pos (Z.pred x) = Pos.pred (Z.to_pos x).
Proof. Show. Fail (abduce 3). Admitted.

Lemma inj_mul x y : 0 < x -> 0 < y ->
 Z.to_pos (x*y) = (Z.to_pos x * Z.to_pos y)%positive.
Proof. Show. Fail (abduce 3). Admitted.

Lemma inj_pow x y : 0 < x -> 0 < y ->
 Z.to_pos (x^y) = (Z.to_pos x ^ Z.to_pos y)%positive.
Proof. Show. Fail (abduce 3). Admitted.

Lemma inj_pow_pos x p : 0 < x ->
 Z.to_pos (Z.pow_pos x p) = ((Z.to_pos x)^p)%positive.
Proof. Show. Fail (abduce 3). Admitted.

Lemma inj_compare x y : 0 < x -> 0 < y ->
 (x ?= y) = (Z.to_pos x ?= Z.to_pos y)%positive.
Proof. Show. Fail (abduce 3). Admitted.

Lemma inj_leb x y : 0 < x -> 0 < y ->
 (x <=? y) = (Z.to_pos x <=? Z.to_pos y)%positive.
Proof. Show. Fail (abduce 3). Admitted.

Lemma inj_ltb x y : 0 < x -> 0 < y ->
 (x <? y) = (Z.to_pos x <? Z.to_pos y)%positive.
Proof. Show. Fail (abduce 3). Admitted.

Lemma inj_eqb x y : 0 < x -> 0 < y ->
 (x =? y) = (Z.to_pos x =? Z.to_pos y)%positive.
Proof. Show. Fail (abduce 3). Admitted.

Lemma inj_max x y :
 Z.to_pos (Z.max x y) = Pos.max (Z.to_pos x) (Z.to_pos y).
Proof. Show. Fail (abduce 3). Admitted.

Lemma inj_min x y :
 Z.to_pos (Z.min x y) = Pos.min (Z.to_pos x) (Z.to_pos y).
Proof. Show. Fail (abduce 3). Admitted.

Lemma inj_sqrt x : Z.to_pos (Z.sqrt x) = Pos.sqrt (Z.to_pos x).
Proof. Show. Fail (abduce 3). Admitted.

Lemma inj_gcd x y : 0 < x -> 0 < y ->
 Z.to_pos (Z.gcd x y) = Pos.gcd (Z.to_pos x) (Z.to_pos y).
Proof. Show. Fail (abduce 3). Admitted.

End Z2Pos.

(** Compatibility Notations *)

Notation Zdouble_plus_one := Z.succ_double (only parsing).
Notation Zdouble_minus_one := Z.pred_double (only parsing).
Notation ZPminus := Z.pos_sub (only parsing).
Notation Zplus := Z.add (only parsing). (* Slightly incompatible *)
Notation Zminus := Z.sub (only parsing).
Notation Zmult := Z.mul (only parsing).
Notation Z_of_nat := Z.of_nat (only parsing).
Notation Z_of_N := Z.of_N (only parsing).

Notation Zind := Z.peano_ind (only parsing).
Notation Zplus_0_l := Z.add_0_l (only parsing).
Notation Zplus_0_r := Z.add_0_r (only parsing).
Notation Zplus_comm := Z.add_comm (only parsing).
Notation Zopp_plus_distr := Z.opp_add_distr (only parsing).
Notation Zplus_opp_r := Z.add_opp_diag_r (only parsing).
Notation Zplus_opp_l := Z.add_opp_diag_l (only parsing).
Notation Zplus_assoc := Z.add_assoc (only parsing).
Notation Zplus_permute := Z.add_shuffle3 (only parsing).
Notation Zplus_reg_l := Z.add_reg_l (only parsing).
Notation Zplus_succ_l := Z.add_succ_l (only parsing).
Notation Zplus_succ_comm := Z.add_succ_comm (only parsing).
Notation Zsucc_discr := Z.neq_succ_diag_r (only parsing).
Notation Zsucc'_discr := Z.neq_succ_diag_r (only parsing).
Notation Zminus_0_r := Z.sub_0_r (only parsing).
Notation Zminus_diag := Z.sub_diag (only parsing).
Notation Zminus_plus_distr := Z.sub_add_distr (only parsing).
Notation Zminus_succ_r := Z.sub_succ_r (only parsing).
Notation Zminus_plus := Z.add_simpl_l (only parsing).
Notation Zmult_0_l := Z.mul_0_l (only parsing).
Notation Zmult_0_r := Z.mul_0_r (only parsing).
Notation Zmult_1_l := Z.mul_1_l (only parsing).
Notation Zmult_1_r := Z.mul_1_r (only parsing).
Notation Zmult_comm := Z.mul_comm (only parsing).
Notation Zmult_assoc := Z.mul_assoc (only parsing).
Notation Zmult_permute := Z.mul_shuffle3 (only parsing).
Notation Zmult_1_inversion_l := Z.mul_eq_1 (only parsing).
Notation Zdouble_mult := Z.double_spec (only parsing).
Notation Zdouble_plus_one_mult := Z.succ_double_spec (only parsing).
Notation Zopp_mult_distr_l_reverse := Z.mul_opp_l (only parsing).
Notation Zmult_opp_opp := Z.mul_opp_opp (only parsing).
Notation Zmult_opp_comm := Z.mul_opp_comm (only parsing).
Notation Zopp_eq_mult_neg_1 := Z.opp_eq_mul_m1 (only parsing).
Notation Zmult_plus_distr_r := Z.mul_add_distr_l (only parsing).
Notation Zmult_plus_distr_l := Z.mul_add_distr_r (only parsing).
Notation Zmult_minus_distr_r := Z.mul_sub_distr_r (only parsing).
Notation Zmult_reg_l := Z.mul_reg_l (only parsing).
Notation Zmult_reg_r := Z.mul_reg_r (only parsing).
Notation Zmult_succ_l := Z.mul_succ_l (only parsing).
Notation Zmult_succ_r := Z.mul_succ_r (only parsing).

Notation Zpos_xI := Pos2Z.inj_xI (only parsing).
Notation Zpos_xO := Pos2Z.inj_xO (only parsing).
Notation Zneg_xI := Pos2Z.neg_xI (only parsing).
Notation Zneg_xO := Pos2Z.neg_xO (only parsing).
Notation Zopp_neg := Pos2Z.opp_neg (only parsing).
Notation Zpos_succ_morphism := Pos2Z.inj_succ (only parsing).
Notation Zpos_mult_morphism := Pos2Z.inj_mul (only parsing).
Notation Zpos_minus_morphism := Pos2Z.inj_sub (only parsing).
Notation Zpos_eq_rev := Pos2Z.inj (only parsing).
Notation Zpos_plus_distr := Pos2Z.inj_add (only parsing).
Notation Zneg_plus_distr := Pos2Z.add_neg_neg (only parsing).

Notation Z := Z (only parsing).
Notation Z_rect := Z_rect (only parsing).
Notation Z_rec := Z_rec (only parsing).
Notation Z_ind := Z_ind (only parsing).
Notation Z0 := Z0 (only parsing).
Notation Zpos := Zpos (only parsing).
Notation Zneg := Zneg (only parsing).

(** Compatibility lemmas. These could be notations,
    but scope information would be lost.
*)

Notation SYM1 lem := (fun n => eq_sym (lem n)).
Notation SYM2 lem := (fun n m => eq_sym (lem n m)).
Notation SYM3 lem := (fun n m p => eq_sym (lem n m p)).

Lemma Zplus_assoc_reverse : forall n m p, n+m+p = n+(m+p).
Proof. Show. Fail (abduce 3). Admitted.
Lemma Zplus_minus : forall n m, n + (m - n) = m.
Proof. Show. Fail (abduce 3). Admitted.
Lemma Zpos_eq_iff : forall p q, p = q <-> Z.pos p = Z.pos q.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Zplus_diag_eq_mult_2 n : n + n = n * 2.
Proof. Show. Fail (abduce 3). Admitted.

Lemma Z_eq_mult n m : m = 0 -> m * n = 0.
Proof. Show. Fail (abduce 3). Admitted.

(** Re-export the notation for those who just [Import BinInt] *)
Number Notation Z Z.of_num_int Z.to_num_hex_int : hex_Z_scope.
Number Notation Z Z.of_num_int Z.to_num_int : Z_scope.