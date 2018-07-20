open CnfSpec
open Rup

(* Some functions to build type use by extracted coq code *)

let mk_literal: (int -> var) -> int -> literal =
  fun mk_var l -> { is_pos = l > 0; ident = mk_var (abs l) }

let mk_clause: (int -> var) -> int list -> clause =
  fun mk_var ->
     List.fold_left (fun c l -> (mk_literal mk_var l)::c) []
    
let mk_cclause: (int -> var) -> int list -> cclause =
  fun mk_var ->
    List.fold_left (fun c l -> Rup.add (mk_literal mk_var l) c) Rup.empty

let mk_cnf: (int -> var) -> int list list -> cnf =
  fun mk_var ->
    List.fold_left (fun f c -> (mk_clause mk_var c)::f) []
