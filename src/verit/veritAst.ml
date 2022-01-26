open SmtBtype
open SmtAtom
open SmtForm
open VeritSyntax

type term = 
  | True
  | False
  | Not of term
  | And of term list
  | Or of term list
  | Imp of term list
  | Xor of term list
  | Ite of term * term * term
  | Forall of (string * typ) list * term
  | Eq of term * term
  | App of string * (term list)
  | Var of string
  | STerm of string (* Shared term *)
  | NTerm of string * term (* Named term *)
  | Int of int (* change to bigint *)
  | Lt of term * term
  | Leq of term * term
  | Gt of term * term
  | Geq of term * term
  | UMinus of term
  | Plus of term * term
  | Minus of term * term 
  | Mult of term * term


type typ = 
  | Int
  | Bool

type clause = term list
type id = string
type params = id list
type args = (term * term) list
type rule = 
  | AssumeAST
  | TrueAST
  | FalsAST
  | NotnotAST
  | ThresoAST
  | ResoAST
  | TautAST
  | ContAST
  | ReflAST
  | TransAST
  | CongAST
  | EqreAST
  | EqtrAST
  | EqcoAST
  | EqcpAST
  | AndAST
  | NorAST
  | OrAST
  | NandAST
  | Xor1 AST
  | Xor2AST
  | Nxor1 AST
  | Nxor2AST
  | ImpAST
  | Nimp1AST
  | Nimp2AST
  | Equ1AST
  | Equ2AST
  | Nequ1AST
  | Nequ2AST
  | AndpAST
  | AndnAST
  | OrpAST
  | OrnAST
  | Xorp1AST
  | Xorp2AST
  | Xorn1AST
  | Xorn2AST
  | ImppAST
  | Impn1AST
  | Impn2AST
  | Equp1AST
  | Equp2AST
  | Equn1AST
  | Equn2AST
  | Ite1AST
  | Ite2AST
  | Itep1AST
  | Itep2AST
  | Iten1AST
  | Iten2AST
  | Nite1AST
  | Nite2AST
  | ConndefAST
  | AndsimpAST
  | OrsimpAST
  | NotsimpAST
  | ImpsimpAST
  | EqsimpAST
  | BoolsimpAST
  | AcsimpAST
  | ItesimpAST
  | EqualsimpAST
  | DistelimAST
  | LageAST
  | LiageAST
  | LataAST
  | LadeAST
  | DivsimpAST
  | ProdsimpAST
  | UminussimpAST
  | MinussimpAST
  | SumsimpAST
  | CompsimpAST
  | LarweqAST
  | BindAST
  | FinsAST
  | QcnfAST
  | AnchorAST
  | SubproofAST of certif

and step = (id, rule, clause, params, args)
and certif = step list

let mk_step (s : (id,rule,clause,params,args)) : step = s
let mk_cl (ts : term list) : clause = ts


(* Remove notnot rule from certificate *)

let get_id (s : step ) : id = 
match s with
| (i, _, _, _, _) -> i

(* Remove element from list *)
let rec remove x l =
  match l with
  | h :: t -> if h == x then remove x t else h :: (remove x t)
  | [] -> []

(* Remove premise from all resolutions in certif *)
let rec remove_res_premise (i : id) (c : certif) : certif =
  match c with
  | (i, r, c, p, a) :: t -> 
      match r with
      | Reso | Threso -> (i, r, c, (remove i p), a) :: (remove_res_premise t)
      | _ -> (i, r, c, p, a) :: (remove_res_premise t)

(* Soundly remove all notnot rules from certificate *)
let rec remove_notnot (c : certif) : certif = 
  match c with
  | (i, r, _, _, _) :: t ->
      match r with
      | Notnot -> remove_notnot (remove_res_premise i t)
      | _ -> h :: remove_notnot t
  | [] -> []


(* Convert the sequence of ids in the steps to sequential integers.
   Do this after finishing all the transformations to the certificates 
   that might add/remove steps *)
let ids : (string, string) Hashtbl.t = Hashtbl.create 17
let get_id s = Hashtbl.find ids i
let add_id s i = Hashtbl.add ids s i
let clear_ids () = Hashtbl.clear ids
let to_sequential_ids (c : certif) : certif =
  let rec aux (z : int) (c : certif) : certif = 
    match z, c with
    | z, (i, r, c, p, a) :: t -> add_id i (string_of_int z);
        let z' = string_of_int z in
        let p' = List.map (fun x -> get_id x) p in
        (z', r, c, p', a) :: aux (z+1) t
  in clear_ids; aux 1 c


(* Convert an AST to a linked list of clauses *)

let rec process_vars (vs (string * typ) list): (string * typ) list = 
  match vs with`
  | (s, t) :: tl -> add_qvar s t; (s, t) :: process_vars tl
  | [] -> []

let rec process_term (t : term) : bool * SmtAtom.Form.t option =
  let decl, t' = (match t with
  | True -> true, Form.Form Form.pform_true
  | False -> true, Form.Form Form.pform_false
  | Not t -> let decl, t' = process_term t in
                 decl, Form.Lit (Form.neg t')
  | And ts -> let ts' = List.map process_term ts in
              apply_dec (fun x -> Form.Form (Fapp (Fand, Array.of_list x)))
                        (list_dec ts')
  | Or ts -> let ts' = List.map process_term ts in
             apply_dec (fun x -> Form.Form (Fapp (For, Array.of_list x)))
                       (list_dec ts')
  | Imp ts -> let ts' = List.map process_term ts in
              apply_dec (fun x -> Form.Form (Fapp (Fimp, Array.of_list x)))
                        (list_dec ts')
  | Xor ts -> let ts' = List.map process_term ts in
              apply_dec (fun x -> Form.Form (Fapp (Fxor, Array.of_list x)))
                        (list_dec ts')
  | Ite ts -> let ts' = List.map process_term ts in
              apply_dec (fun x -> Form.Form (Fapp (Fite, Array.of_list x)))
                        (list_dec ts')
  | Forall (vs, t) -> let vs' = process_vars vs in
                      let t' = process_term t in
                      clear_qvar ();
                      false, Form.Form (Fapp (Fforall vs', 
                                             [|Form.lit_of_atom_form_lit rf t'|]))
  | Eq (t1, t2) -> let t1' = process_term t1 in
                   let t2' = process_term t2 in
      match t1', t2' with 
      | (decl1, Form.Atom h1), (decl2, Form.Atom h2) 
          when (match Atom.type_of h1 with 
                | SmtBtype.Tbool -> false 
                | _ -> true)                          -> 
        decl1 && decl2, Form.Atom (Atom.mk_eq_sym ra ~declare:decl (Atom.type_of h1) h1 h2) 
      | (decl1, t1), (decl2, t2) -> decl1 && decl2, 
          Form.Form (Fapp (Fiff, [|Form.lit_of_atom_form_lit rf (decl1, t1); 
                                   Form.lit_of_atom_form_lit rf (decl2, t2)|]))
  | App (f, ts) -> let ts' = List.map process_term ts in
                   let args = (fun x -> match x with 
                               | decl, Form.Atom h -> (decl, h)
                               | _ -> assert false) ts' in
      match find_opt_qvar f with
      | Some bt -> let op = dummy_indexed_op (Rel_name f) [||] bt in
                   false, Form.Atom (Atom.get ~declare:false ra (Aapp (op, Array.of_list (snd (list_dec args))))) 
      | None ->    let dl, l = list_dec args in 
                   dl, Form.Atom (Atom.get ra ~declare:dl (Aapp (SmtMaps.get_fun f, Array.of_list l)))
  | Var s -> match find_opt_qvar s with
             | Some bt   -> false, 
                Form.Atom (Atom.get ~declare:false ra (Aapp (dummy_indexed_op (Rel_name s) [||] bt, [||])))
             | None      -> true, Form.Atom (Atom.get ra (Aapp (SmtMaps.get_fun s, [||])))
  | STerm s -> get_solver s
  | NTerm (s, t) -> let t' = process_term t in
                    add_solver s t'
  | Int i -> true, Form.Atom (Atom.hatom_Z_of_int ra i
  | Lt (x,y) -> let x' = process_term x in
                let t' = process_term y in 
                apply_bdec_atom (Atom.mk_lt ra) x' y'
  | Leq (x,y) -> let x' = process_term x in
                 let t' = process_term y in 
                 apply_bdec_atom (Atom.mk_le ra) x' y'
  | Gt (x,y) -> let x' = process_term x in
                let t' = process_term y in 
                apply_bdec_atom (Atom.mk_gt ra) x' y'
  | Geq (x,y) -> let x' = process_term x in
                 let y' = process_term y in 
                 apply_bdec_atom (Atom.mk_ge ra) x' y'
  | UMinus t -> let t' = process_term t in
                apply_dec_atom (fun ?declare:d a -> Atom.mk_neg ra a) t
  | Plus (x,y) -> let x' = process_term x in
                  let y' = process_term y in 
                  apply_bdec_atom (Atom.mk_plus ra) x' y'
  | Minus (x,y) -> let x' = process_term x in
                   let t' = process_term y in
                   apply_bdec_atom (Atom.mk_minus ra) x' y'
  | Mult (x,y) -> let x' = process_term x in
                  let t' = process_term y in
                  apply_bdec_atom (Atom.mk_mult ra) x' y') 
  in
  decl, Form.lit_of_atom_form_lit rf (decl, t')

let process_cl (c : cl) : SmtAtom.Form.t opton list =
  let _, l = list_dec (List.map process_term cl) in l

let process_rule (r: rule) : VeritSyntax.typ =
  match r with
  | AssumeAST -> Assume
  | TrueAST -> True
  | FalsAST -> Fals
  | NotnotAST -> Notnot
  | ThresoAST -> Threso
  | ResoAST -> Reso
  | TautAST -> Taut
  | ContAST -> Cont
  | ReflAST -> Refl
  | TransAST -> Trans
  | CongAST -> Cong
  | EqreAST -> Eqre
  | EqtrAST -> Eqtr
  | EqcoAST -> Eqco
  | EqcpAST -> Eqcp
  | AndAST -> And
  | NorAST -> Nor
  | OrAST -> Or
  | NandAST -> Nand
  | Xor1 AST -> Xor1 
  | Xor2AST -> Xor2
  | Nxor1 AST -> Nxor1 
  | Nxor2AST -> Nxor2
  | ImpAST -> Imp
  | Nimp1AST -> Nimp1
  | Nimp2AST -> Nimp2
  | Equ1AST -> Equ1
  | Equ2AST -> Equ2
  | Nequ1AST -> Nequ1
  | Nequ2AST -> Nequ2
  | AndpAST -> Andp
  | AndnAST -> Andn
  | OrpAST -> Orp
  | OrnAST -> Orn
  | Xorp1AST -> Xorp1
  | Xorp2AST -> Xorp2
  | Xorn1AST -> Xorn1
  | Xorn2AST -> Xorn2
  | ImppAST -> Impp
  | Impn1AST -> Impn1
  | Impn2AST -> Impn2
  | Equp1AST -> Equp1
  | Equp2AST -> Equp2
  | Equn1AST -> Equn1
  | Equn2AST -> Equn2
  | Ite1AST -> Ite1
  | Ite2AST -> Ite2
  | Itep1AST -> Itep1
  | Itep2AST -> Itep2
  | Iten1AST -> Iten1
  | Iten2AST -> Iten2
  | Nite1AST -> Nite1
  | Nite2AST -> Nite2
  | ConndefAST -> Conndef
  | AndsimpAST -> Andsimp
  | OrsimpAST -> Orsimp
  | NotsimpAST -> Notsimp
  | ImpsimpAST -> Impsimp
  | EqsimpAST -> Eqsimp
  | BoolsimpAST -> Boolsimp
  | AcsimpAST -> Acsimp
  | ItesimpAST -> Itesimp
  | EqualsimpAST -> Equalsimp
  | DistelimAST -> Distelim
  | LageAST -> Lage
  | LiageAST -> Liage
  | LataAST -> Lata
  | LadeAST -> Lade
  | DivsimpAST -> Divsimp
  | ProdsimpAST -> Prodsimp
  | UminussimpAST -> Uminussimp
  | MinussimpAST -> Minussimp
  | SumsimpAST -> Sumsimp
  | CompsimpAST -> Compsimp
  | LarweqAST -> Larweq
  | BindAST -> Bind
  | FinsAST -> Fins
  | QcnfAST -> Qcnf
  | AnchorAST -> Hole
  | SubproofAST c -> Hole

(* let symbol_to_id = int_of_string *)
let symbol_to_id s = 
  (* f transforms string "tn" to int n *)
  let f = (fun s -> let l = (String.length s) - 1 in
                    int_of_string (String.sub s 1 l)) in
  (* Subproof steps have labels*)                  
  let syms = List.map f (String.split_on_char '.' s) in
  if (List.length syms == 1) then 
    List.hd syms
  else 
    raise InvalidProofStepNo

let rec process_certif (c : certif) : SmtCertif.clause_id list =
  match c with
  | (i, r, c, p, a) :: t -> 
      let i' = symbol_to_id i in
      let r' = process_rule r in
      let c' = process_cl c in
      let p' = List.map symbol_to_id p in
      mk_clause (i', r', c', p', a) :: process_certif t
  | [] -> []