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


val cInt_tbl : (int, CoqInterface.constr) Hashtbl.t
val mkInt : int -> CoqInterface.constr
type 'a gen_hashed = { index : int; mutable hval : 'a; }
val mklApp : CoqInterface.constr Lazy.t -> CoqInterface.constr array -> CoqInterface.constr
val string_of_name_def : string -> CoqInterface.name -> string
val string_coq_constr : CoqInterface.constr -> string
type logic_item = LUF | LLia | LBitvectors | LArrays
module SL : Set.S with type elt = logic_item
type logic = SL.t

(** Utils *)
val filter_map : ('a -> 'b option) -> 'a list -> 'b list

(** Lexing *)
val char_for_backslash : char -> char
val lf : char
val dec_code : char -> char -> char -> int
val hex_code : char -> char -> int
val found_newline : Lexing.lexbuf -> int -> unit
val lexeme_len : Lexing.lexbuf -> int
val main_failure : Lexing.lexbuf -> string -> 'a

(** Constr hashtables up to aliasing, casts, ... *)
module ConstrHashtbl : sig
  type 'a t
  val create : int -> 'a t
  val add : 'a t -> CoqInterface.constr -> 'a -> unit
  val find : 'a t -> CoqInterface.constr -> 'a
  val clear : 'a t -> unit
end
