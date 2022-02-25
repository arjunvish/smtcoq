(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2022                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


type used = int

type clause_id  = int

type 'hform rule =
  (* Weakening *)
  | Weaken of 'hform clause * 'hform list
    (*  * weaken          : {a_1 ... a_n} --> {a_1 ... a_n b_1 ... b_n} *)

  (* Simplification *)
  | ImmFlatten of 'hform clause * 'hform

  (* CNF Transformations *)
  | True
    (*  * true            : {true} *)
  | False
    (* * false            : {(not false)} *)
  | NotNot of 'hform
    (* * notnot           : {(not not x) --> x} *)
  | Tautology of 'hform clause * 'hform
    (* * tautology        : {(x_1 ... x_i ... (not x_i) ... x_n) --> true)} *)
  | Contraction of 'hform clause * 'hform list
    (* * contraction      : {(x_1 ... x_n) --> (x_k1 ... x_kn)}, 
          where duplicates are removed and order is preserved 
    *)
  | BuildDef of 'hform (* the first literal of the clause *)
    (* * and_neg          : {(and a_1 ... a_n) (not a_1) ... (not a_n)}
       * or_pos           : {(not (or a_1 ... a_n)) a_1 ... a_n}
       * implies_pos      : {(not (implies a b)) (not a) b}
       * xor_pos1         : {(not (xor a b)) a b}
       * xor_neg1         : {(xor a b) a (not b)}
       * equiv_pos1       : {(not (iff a b)) a (not b)}
       * equiv_neg1       : {(iff a b) (not a) (not b)}
       * ite_pos1         : {(not (if_then_else a b c)) a c}
       * ite_neg1         : {(if_then_else a b c) a (not c)}
    *)
  | BuildDef2 of 'hform (* the first literal of the clause *)
    (* * xor_pos2         : {(not (xor a b)) (not a) (not b)}
       * xor_neg2         : {(xor a b) (not a) b}
       * equiv_pos2       : {(not (iff a b)) (not a) b}
       * equiv_neg2       : {(iff a b) a b}
       * ite_pos2         : {(not (if_then_else a b c)) (not a) b}
       * ite_neg2         : {(if_then_else a b c) (not a) (not b)}
    *)
  | BuildProj of 'hform * int
    (* * or_neg           : {(or a_1 ... a_n) (not a_i)}
       * and_pos          : {(not (and a_1 ... a_n)) a_i}
       * implies_neg1     : {(implies a b) a}
       * implies_neg2     : {(implies a b) (not b)}
    *)

  (* Immediate CNF transformation : CNF transformation + Reso *)
  | ImmBuildDef of 'hform clause
    (* * not_and          : {(not (and a_1 ... a_n))} --> {(not a_1) ... (not a_n)}
       * or               : {(or a_1 ... a_n)} --> {a_1 ... a_n}
       * implies          : {(implies a b)} --> {(not a) b}
       * xor1             : {(xor a b)} --> {a b}
       * not_xor1         : {(not (xor a b))} --> {a (not b)}
       * equiv2           : {(iff a b)} --> {a (not b)}
       * not_equiv2       : {(not (iff a b))} --> {(not a) (not b)}
       * ite1             : {(if_then_else a b c)} --> {a c}
       * not_ite1         : {(not (if_then_else a b c))} --> {a (not c)}
    *)
  | ImmBuildDef2 of 'hform clause
    (* * xor2             : {(xor a b)} --> {(not a) (not b)}
       * not_xor2         : {(not (xor a b))} --> {(not a) b}
       * equiv1           : {(iff a b)} --> {(not a) b}
       * not_equiv1       : {(not (iff a b))} --> {a b}
       * ite2             : {(if_then_else a b c)} --> {(not a) b}
       * not_ite2         : {(not (if_then_else a b c))} --> {(not a) (not b)}
    *)
  | ImmBuildProj of 'hform clause * int
    (* * and              : {(and a_1 ... a_n)} --> {a_i}
       * not_or           : {(not (or a_1 ... a_n))} --> {(not a_i)}
       * not_implies1     : {(not (implies a b))} --> {a}
       * not_implies2     : {(not (implies a b))} --> {(not b)}
    *)

  (* Simplification Rules *)
  | NotSimplify of 'hform
    (* *  not_simplify    : {iff (not (not x)) x}
                            {iff (not false) true}
                            {iff (not true) false}
    *)
  | AndSimplify of 'hform
    (* * and_simplify     : {iff (and true ... true) true}
                            {iff (and x_1 ... x_n) (and x_1 ... x_n'), removing all true from x_1,...,x_n}
                            {iff (and x_1 ... x_n) (and x_1 ... x_n'), removing all repeated literals from x_1,...,x_n}
                            {iff (and x_1 ... false ... x_n) false}
                            {iff (and x_1 ... x_i ... x_j ... x_n) false, if x_i = not x_j}
    *)
  | OrSimplify of 'hform
    (* * or_simplify      : {iff (or false ... false) false}
                            {iff (or x_1 ... x_n) (or x_1 ... x_n'), removing all false from x_1,...,x_n}
                            {iff (or x_1 ... x_n) (or x_1 ... x_n'), removing all repeated literals from x_1,...,x_n}
                            {iff (or x_1 ... true ... x_n) true}
                            {iff (or x_1 ... x_i ... x_j ... x_n) true, if x_i = not x_j}
    *)
  | ImpSimplify of 'hform
    (* * implies_simplify : {iff (not x -> not y) (y -> x)}
                            {iff (false -> x) true}
                            {iff (x -> true) true}
                            {iff (true -> x) x}
                            {iff (x -> false) (not x)}
                            {iff (x -> x) true}
                            {iff (not x -> x) x}
                            {iff (x -> not x) (not x)}
                            {iff ((x -> y) -> y) (or x y)}
      *)
  | EquivSimplify of 'hform
    (* * equiv_simplify   : {iff (iff (not x) (not y)) (iff x y)}
                            {iff (iff x x) true}
                            {iff (iff x (not x)) false}
                            {iff (iff (not x) x) false}
                            {iff (iff true x) x}
                            {iff (iff x true) x}
                            {iff (iff false x) (not x)}
                            {iff (iff x false) (not x)}
    *)
  | BoolSimplify of 'hform
    (* * bool_simplify   :  {iff (not (x -> y)) (and x (not y))}
                            {iff (not (or x y)) (and (not x) (not y))}
                            {iff (not (and x y)) (or (not x) (not y))}
                            {iff (x -> (y -> z)) ((and x y) -> z)}
                            {iff ((x -> y) -> y) (or x y)}
                            {iff (and x (x -> y)) (and x y)}
                            {iff (and (x -> y) x) (and x y)}
     *)
  | ConnDef of 'hform
    (* * connective_def  :  {iff (xor x y) (or (and (not x) y) (and x (not y)))}
                            {iff (iff x y) (and (x -> y) (y -> x)))}
                            {iff (ite f x y) (and (f -> x) ((not f) -> (not y))))}
    *)
  | IteSimplify of 'hform
    (* * ite_simplify    :  {iff (ite true x y) x}
                            {iff (ite false x y) y)}
                            {iff (ite f x x) x}
                            {iff (ite (not f) x y) (ite f y x)}
                            {iff (ite f (ite f x y) z) (ite f x z)}
                            {iff (ite f x (ite f y z)) (ite f x z)}
                            {iff (ite f true false) f}
                            {iff (ite f false true) (not f)}
                            {iff (ite f true x) (or f x)}
                            {iff (ite f x false) (and f x)}
                            {iff (ite f false x) (and (not f) x)}
                            {iff (ite f x true) (or (not f) x)}
    *)
  | EqSimplify of 'hform
    (* * eq_simplify     :  {iff (x = x) true}
                            {iff (x = y) false} if x and y are different numeric constants
                            {iff (not (x = x)) false} if x is a numeric constant
    *)
  | DistElim  of 'hform list * 'hform
    (* * distinct_elim   :  {iff (distinct x) y where distinct is eliminated in y} *)
  
  (* Equality *)
  | EqTr of 'hform * 'hform list
    (* * eq_reflexive    : {(= x x)}
       * eq_transitive   : {(not (= x_1 x_2)) ... (not (= x_{n-1} x_n)) (= x_1 x_n)}
    *)
  | EqCgr of 'hform * ('hform option) list
    (* * eq_congruent    : {(not (= x_1 y_1)) ... (not (= x_n y_n))
                            (= (f x_1 ... x_n) (f y_1 ... y_n))}
    *)
  | EqCgrP of 'hform * 'hform * ('hform option) list
    (* * eq_congruent_pred: {(not (= x_1 y_1)) ... (not (= x_n y_n))
                             (not (p x_1 ... x_n)) (p y_1 ... y_n)}
    *)
  | IffTrans of ('hform clause) list * 'hform
    (* * trans            : {(= x_1 x_2) --> (= x_2 x_1) --> ... --> (= x_{n-1} x_n) 
                             --> (= x_1 x_n)}
    *)
  | IffCong of ('hform clause) list * 'hform
    (* * cong            : {(= x_1 y_1) --> (= x_2 y_2) --> ... --> (= x_n y_n)
                            --> (= f(x_1, ..., x_n) f(y_1, ..., y_n)
    *)
  
  (* Linear arithmetic *)
  | LiaMicromega of 'hform list * CoqInterface.Micromega_plugin_Certificate.Mc.zArithProof list
  | LiaDiseq of 'hform
  
  (* Arithmetic simplifications *)
  | SplArith of 'hform clause * 'hform * CoqInterface.Micromega_plugin_Certificate.Mc.zArithProof list

  (* Elimination of operators *)
  | SplDistinctElim of 'hform clause * 'hform

  (* Bit-blasting *)
  | BBVar of 'hform
    (* Bit-blasting a variable:

       ----------------------- bbVar
        bbT(x, [x0; ...; xn])
    *)
  | BBConst of 'hform
    (* Bit-blasting a constant:

       ----------------------- bbConst
        bbT(#0100, [0; 0; 1; 0])
    *)
  | BBOp of 'hform clause * 'hform clause * 'hform
    (* Bit-blasting bitwise operations: bbAnd, bbOr, ...
        bbT(a, [a0; ...; an])      bbT(b, [b0; ...; bn])
       -------------------------------------------------- bbAnd
             bbT(a&b, [a0 /\ b0; ...; an /\ bn])
    *)
  | BBNot of 'hform clause * 'hform
    (* Bit-blasting bitvector not
           bbT(a, [a0; ...; an])
       ------------------------------ bbNot
        bbT(not a, [~a0 ; ...; ~an])
    *)
  | BBNeg of 'hform clause * 'hform
    (* Bit-blasting bitvector negation
           bbT(a, [a0; ...; an])
       ------------------------------ bbNot
        bbT(-a, [...])
    *)
  | BBAdd of 'hform clause * 'hform clause * 'hform
    (* Bit-blasting bitvector addition
        bbT(a, [a0; ...; an])      bbT(b, [b0; ...; bn])
       -------------------------------------------------- bbAnd
             bbT(a+b, [...])
    *)
  | BBMul of 'hform clause * 'hform clause * 'hform
    (* Bit-blasting bitvector multiplication
        bbT(a, [a0; ...; an])      bbT(b, [b0; ...; bn])
       -------------------------------------------------- bbAnd
             bbT(a*b, [...])
    *)
  | BBUlt of 'hform clause * 'hform clause * 'hform
    (* Bit-blasting bitvector unsigned comparison
        bbT(a, [a0; ...; an])      bbT(b, [b0; ...; bn])
       -------------------------------------------------- bbAnd
             bvult a b <-> ...
    *)
  | BBSlt of 'hform clause * 'hform clause * 'hform
    (* Bit-blasting bitvector signed comparison
        bbT(a, [a0; ...; an])      bbT(b, [b0; ...; bn])
       -------------------------------------------------- bbAnd
             bvslt a b <-> ...
    *)
  | BBConc of 'hform clause * 'hform clause * 'hform
    (* Bit-blasting bitvector concatenation
        bbT(a, [a0; ...; an])      bbT(b, [b0; ...; bn])
       -------------------------------------------------- bbConc
             bbT(concat a b, [a0; ...; an; b0; ...; bn])
    *)
  | BBExtr of 'hform clause * 'hform
    (* Bit-blasting bitvector extraction
             bbT(a, [a0; ...; an])
       ----------------------------------- bbExtr
        bbT(extract i j a, [ai; ...; aj])
    *)
  | BBZextn of 'hform clause * 'hform
  | BBSextn of 'hform clause * 'hform
    (* Bit-blasting bitvector extensions *)
  | BBShl of 'hform clause * 'hform clause * 'hform
    (* Bit-blasting bitvector shift left *)
  | BBShr of 'hform clause * 'hform clause * 'hform
    (* Bit-blasting bitvector shift right *)
  | BBEq of 'hform clause * 'hform clause * 'hform
    (* Bit-blasting equality
        bbT(a, [a0; ...; an])      bbT(b, [b0; ...; bn])
       -------------------------------------------------- bbEq
         (a = b) <-> [(a0 <-> b0) /\ ... /\ (an <-> bn)]
    *)
  | BBDiseq of 'hform
    (* disequality over constant bitvectors

       ----------------------------- bbDiseq
         #b000010101 <> #b00000000
    *)

  (* Arrays *)
  | RowEq of 'hform
    (* Read over write same index
       ------------------------------- roweq
         select (store a i v) i = v
    *)
  | RowNeq of 'hform list
    (* Read over write other index
       ------------------------------------------------- rowneq
         i <> j -> select (store a i v) j = select a j
    *)
  | Ext of 'hform
    (* Extensionality over arrays
       ------------------------------------------------------- ext
         a = b \/ select a (diff a b) <> select b (diff a b)
    *)

  (* *  ident    : {x --> x}
  *)
  | Ident of 'hform clause

  (* Possibility to introduce "holes" in proofs (that should be filled in Coq) *)
  | Hole of ('hform clause) list * 'hform list

  (* Quantifiers *)
  | Forall_inst of 'hform clause * 'hform
  | Qf_lemma of 'hform clause * 'hform

and 'hform clause = {
    mutable id    : clause_id;
    mutable kind  : 'hform clause_kind;
    mutable pos   : int option;
    mutable used  : used;
    mutable prev  : 'hform clause option;
    mutable next  : 'hform clause option;
    mutable value : 'hform list option
              (* This field should be defined for rules which can create atoms :
                 EqTr, EqCgr, EqCgrP, Lia, Dlde, Lra *)
}

and 'hform clause_kind =
  | Root
  | Same of 'hform clause
  | Res of 'hform resolution
  | Other of 'hform rule

and 'hform resolution = {
  mutable rc1   : 'hform clause;
  mutable rc2   : 'hform clause;
  mutable rtail : 'hform clause list}

let used_clauses r =
  match r with
  | ImmBuildProj (c, _) | ImmBuildDef c | ImmBuildDef2 c
  | Tautology (c, _) | Contraction (c,_) | Weaken (c,_) 
  | ImmFlatten (c,_) | SplArith (c,_,_) | SplDistinctElim (c,_)
  | BBNot (c, _) | BBNeg (c, _) | BBExtr (c, _)
  | BBZextn (c, _) | BBSextn (c, _) | Ident c -> [c]

  | BBOp (c1,c2,_) | BBAdd (c1,c2,_)
  | BBMul (c1,c2,_) | BBConc (c1,c2,_)
  | BBUlt (c1,c2,_) | BBSlt (c1,c2,_)
  | BBShl (c1,c2,_) | BBShr (c1,c2,_)
  | BBEq (c1,c2,_) -> [c1;c2]

  | Hole (cs, _) | IffTrans (cs, _) | IffCong (cs, _) -> cs
  | Forall_inst (c, _) | Qf_lemma (c, _) -> [c]

  | True | False | NotNot _ | BuildDef _ 
  | BuildDef2 _ | BuildProj _ | NotSimplify _ 
  | AndSimplify _ | OrSimplify _ | ImpSimplify _ 
  | EquivSimplify _ | BoolSimplify _ | ConnDef _
  | IteSimplify _ | EqSimplify _ | DistElim _
  | EqTr _ | EqCgr _ | EqCgrP _ | LiaMicromega _ 
  | LiaDiseq _ | BBVar _ | BBConst _ | BBDiseq _
  | RowEq _ | RowNeq _ | Ext _ -> []

(* For debugging certif processing purposes : <add_scertif> <select> <occur> <alloc> *)
let to_string r =
  match r with
            Root -> "Root"
          | Same c -> "Same(" ^ string_of_int (c.id) ^ ")"
          | Res r ->
             let id1 = string_of_int r.rc1.id in
             let id2 = string_of_int r.rc2.id in
             let rest_ids = List.fold_left (fun str rc -> str ^ "; " ^ string_of_int rc.id) "" r.rtail in
             "Res [" ^ id1 ^ "; " ^ id2 ^ rest_ids ^"]"
          | Other x -> "Other(" ^
                         begin match x with
                           | Weaken _ -> "Weaken"
                           | ImmFlatten _ -> "ImmFlatten"
                           | True -> "True"
                           | False -> "False"
                           | NotNot _ -> "NotNot"
                           | Tautology _ -> "Tautology"
                           | Contraction _ -> "Contraction"
                           | BuildDef _ -> "BuildDef"
                           | BuildDef2 _ -> "BuildDef2"
                           | BuildProj _ -> "BuildProj"
                           | ImmBuildDef _ -> "ImmBuildDef"
                           | ImmBuildDef2 _ -> "ImmBuildDef2"
                           | ImmBuildProj _ -> "ImmBuildProj"
                           | NotSimplify _ -> "NotSimplify"
                           | AndSimplify _ -> "AndSimplify"
                           | OrSimplify _ -> "OrSimplify"
                           | ImpSimplify _ -> "ImpSimplify"
                           | EquivSimplify _ -> "EquivSimplify"
                           | BoolSimplify _ -> "BoolSimplify"
                           | ConnDef _ -> "ConnDef"
                           | IteSimplify _ -> "IteSimplify"
                           | EqSimplify _ -> "EqSimplify"
                           | DistElim _ -> "DistElim"
                           | EqTr _ -> "EqTr"
                           | EqCgr _ -> "EqCgr"
                           | EqCgrP _ -> "EqCgrP"
                           | IffTrans _ -> "IffTrans"
                           | IffCong _ -> "IffCong"
                           | LiaMicromega _ -> "LiaMicromega"
                           | LiaDiseq _ -> "LiaDiseq"
                           | SplArith _ -> "SplArith"
                           | SplDistinctElim _ -> "SplDistinctElim"
                           | BBVar _ -> "BBVar"
                           | BBConst _ -> "BBConst"
                           | BBOp _ -> "BBOp"
                           | BBNot _ -> "BBNot"
                           | BBNeg _ -> "BBNeg"
                           | BBAdd _ -> "BBAdd"
                           | BBMul _ -> "BBMul"
                           | BBUlt _ -> "BBUlt"
                           | BBSlt _ -> "BBSlt"
                           | BBConc _ -> "BBConc"
                           | BBExtr _ -> "BBExtr"
                           | BBZextn _ -> "BBZextn"
                           | BBSextn _ -> "BBSextn"
                           | BBShl _ -> "BBShl"
                           | BBShr _ -> "BBShr"
                           | BBEq _ -> "BBEq"
                           | BBDiseq _ -> "BBDiseq"
                           | RowEq _ -> "RowEq"
                           | RowNeq _ -> "RowNeq"
                           | Ext _ -> "Ext"
                           | Ident _ -> "Ident"
                           | Hole _ -> "Hole"
                           | Forall_inst _ -> "Forall_inst"
                           | Qf_lemma _ -> "Qf_lemma"
                         end ^ ")"



(* To use <print_certif>, pass, as first and second argument, <Form.to_smt> and <Atom.to_string> *)
let print_certif form_to_smt atom_to_string c where =
  let rec start c =
    match c.prev with
    | None -> c
    | Some c -> start c in
  let r = ref (start c) in
  let out_channel = open_out where in
  let fmt = Format.formatter_of_out_channel out_channel in
  let continue = ref true in
  while !continue do
    let kind = to_string (!r.kind) in
    let id = !r.id in
    let pos = match !r.pos with
      | None -> "None"
      | Some p -> string_of_int p in
    let used = !r.used in
    Format.fprintf fmt "id:%i kind:%s pos:%s used:%i value:" id kind pos used;
    begin match !r.value with
    | None -> Format.fprintf fmt "None"
    | Some l -> List.iter (fun f -> form_to_smt atom_to_string fmt f;
                                    Format.fprintf fmt " ") l end;
    Format.fprintf fmt "\n";
    match !r.next with
    | None -> continue := false
    | Some n -> r := n 
  done;
  Format.fprintf fmt "@."; close_out out_channel
