open CnfSpec
open SolverInterface
open Rup
open OracleData
open OracleUtils

module IntHash =
struct
  type t = int
  let equal i j = i=j
  let hash i = i land max_int
end

module IntHashtbl = Hashtbl.Make(IntHash)

let ht_size2 = 100;;

let rec get_resolution_clauses_rec =
  fun lc_ht rc acc ->
    match rc with
    | h :: t -> get_resolution_clauses_rec lc_ht t ((IntHashtbl.find lc_ht h)::acc)
    | _ -> acc

(*list of coq clause from a list of clause index*)
let get_resolution_clauses : 'a IntHashtbl.t -> int list -> 'a list =
  fun lc_ht rc ->
    get_resolution_clauses_rec lc_ht rc []

(* delete clauses of the hashtable lc_ht whose index are in list l *)
let rec delete_clauses : 'a IntHashtbl.t -> int list -> unit
  = fun lc_ht l ->
    match l with
    | h::t -> IntHashtbl.remove lc_ht h; delete_clauses lc_ht t
    | [] -> ();;
      
let mkc = mk_cclause;;

let rec mk_learned_clauses_rec : 'a rupLCF -> 'a list -> 'a IntHashtbl.t -> 'a IntHashtbl.t =
  fun rc cnf ht ->
    match cnf with
    | c::t -> (IntHashtbl.add ht (rc.get_id c) c);
               mk_learned_clauses_rec rc t ht
    |_ -> ht;;

(* create an hashtable of coq clause from a list of coq clause *)
let mk_learned_clauses :  'a rupLCF -> 'a list -> 'a IntHashtbl.t
  = fun rc cnf ->
    let ht = IntHashtbl.create (List.length cnf) in
      mk_learned_clauses_rec rc cnf ht

(* convert a list of clause index into a list of coq clause *)
let clc_to_alc : 'a IntHashtbl.t -> int list -> 'a list
  = fun ht_cnf (clc:int list)->
    let rec clc_to_alc_rec =
      fun ht_cnf clc acc ->
	match clc with
	| h::t -> (try clc_to_alc_rec ht_cnf t (IntHashtbl.find ht_cnf h :: acc) with e -> Printf.printf "BLA %d\n%!" h; raise e)
	| _ -> acc
    in
    clc_to_alc_rec ht_cnf clc []

(* convert a list of negative pivot index into a coq list of negative pivot *)
let rec nh_to_iwnp : 'a IntHashtbl.t -> int -> (int list IntHashtbl.t) -> ('a * 'a list)
    = fun ht_cnf e nh ->
    let lc = IntHashtbl.find nh e in
    (IntHashtbl.find ht_cnf e,clc_to_alc ht_cnf lc);;

(* build the coq clauses list without negative pivot and the coq clauses list with negative pivot *)
let mk_iwonp_iwnp : 'a IntHashtbl.t -> (int list IntHashtbl.t) -> 'a list * ('a * 'a list) list
  = fun ht_cnf nh ->
    IntHashtbl.fold  (fun a b c -> let (iwonp,iwnp) = c in
				   try
				     (iwonp,nh_to_iwnp ht_cnf a nh :: iwnp)
				   with
				   |Not_found -> (IntHashtbl.find ht_cnf a :: iwonp,iwnp)
    ) ht_cnf ([],[])
    
open RatTheory
open Datatypes

type ratSingle_ht = {
  new_id: int;
  clause_to_learn: int list;
  propagate_list: int list;
  rup_proofs: (int list) IntHashtbl.t; (* int -> int list *)
}

type ratInput_ht = {
  pivot : int;
  remainder: unit IntHashtbl.t;
  basis: unit IntHashtbl.t;
  bunch: ratSingle_ht IntHashtbl.t ; (*id -> ratSingle_ht*)
}

type ratInput = ratInput_ht option;;

(***** add new rat line in ratInput *****)

let mkRatInput : 'a IntHashtbl.t -> ratLine -> ratInput =
  fun ht_cnf (i,b,ctl,pl,nh) ->
    let pivot = match ctl with |p::c' -> p |nil -> 0 in
    let basis = IntHashtbl.create ht_size2 in
    let remainder = IntHashtbl.create (IntHashtbl.length ht_cnf) in
    let rp = IntHashtbl.create ht_size2 in
    (List.iter (fun (n,l) -> IntHashtbl.add basis (-n) (); IntHashtbl.add rp (-n) l;) nh);
    IntHashtbl.iter (fun a b -> if not (IntHashtbl.mem basis a) then IntHashtbl.add remainder a ()) ht_cnf;
    let rs = { new_id=i; clause_to_learn=ctl; propagate_list=pl; rup_proofs=rp } in
    let bunch_ht = IntHashtbl.create ht_size2 in
    (IntHashtbl.add bunch_ht i rs);
    Some {pivot=pivot; remainder=remainder; basis=basis; bunch=bunch_ht;}

let ri_isEmpty : ratInput -> bool =
  fun ri -> match ri with |None -> true | Some _ -> false

(* check that we can learn the rup clause without distorting the bunch*)
let rec ri_check_rup_ok : ratLine -> ratInput -> bool
  = fun (i,b,ctl,lp,nh) rio->
      match rio with
      | None -> true
      | Some ri ->(
	not (List.mem (-ri.pivot) ctl) &&
	not (List.exists (fun a -> IntHashtbl.mem ri.bunch a) lp) &&
	match nh with
	| [] -> true
	| (n,p)::t -> if IntHashtbl.mem ri.bunch (-n) || (List.exists (fun a -> IntHashtbl.mem ri.bunch a) p) then false else ri_check_rup_ok (i,b,ctl,lp,t) rio)
	 
exception Different_pivot;;
exception Different_basis;;
exception In_bunch;;

(* build ratInput's rup_proofs, check Different_basis and In_bunch *)
let mk_rup_proofs : ratInput_ht -> ratLine -> (int list) IntHashtbl.t
  = fun ri (i,b,ctl,pl,nh) ->
     let rp = IntHashtbl.create ht_size2 in
     (* check pl clause not in bunch: *)
     if (List.exists (fun a -> IntHashtbl.mem ri.bunch a) pl) then raise In_bunch;
     (* check nh (negative and positive hint) not in bunch and add proofs to rp *)
     (List.iter
	(fun (n,l) ->
	  let n = -n in
	  if IntHashtbl.mem ri.bunch n || (List.exists (fun a -> IntHashtbl.mem ri.bunch a) l)
	  then raise In_bunch
	  else if not (IntHashtbl.mem ri.basis n) then
	    raise Different_basis
	  else IntHashtbl.add rp n l;)
	nh);
     if not(IntHashtbl.length ri.basis = List.length nh) then raise Different_basis;
     rp;;

(* add ratSingle_ht to ratInput_ht *)
let ri_add_rs : ratInput_ht -> ratLine-> unit =
  fun ri (i,b,ctl,pl,nh)->
    let pivot = match ctl with |p::c' -> p |nil -> 0 in
    (* check same pivot *)
    (if not (pivot = ri.pivot) then raise Different_pivot);
    (* build rup_proofs and check Different_basis,In_bunch *)
    let rp = mk_rup_proofs ri (i,b,ctl,pl,nh) in
    let rs = { new_id=i; clause_to_learn=ctl; propagate_list=pl; rup_proofs=rp } in
    IntHashtbl.add ri.bunch i rs;;

(* add ratLine to ratInput *)
let ri_add : 'a IntHashtbl.t -> ratInput -> ratLine -> ratInput =
  fun ht_cnf ri rl ->
    match ri with
    | None ->
       mkRatInput ht_cnf rl
    | Some ri -> ri_add_rs ri rl; Some ri

let rec ri_delete_clause : ratInput_ht -> int list -> ratInput = (* TODO: tests printf *)
  fun ri l ->
    match l with
    | [] -> if IntHashtbl.length ri.bunch = 0 then (Printf.printf "bunch emptied\n%!"; None) else Some ri
    | h::q ->
       (try
	  let _ = IntHashtbl.find ri.remainder h in IntHashtbl.remove ri.remainder h
	with
	|Not_found -> Printf.printf "delete basis\n%!"; IntHashtbl.remove ri.basis h; IntHashtbl.iter (fun a b -> IntHashtbl.remove b.rup_proofs h) ri.bunch);
      IntHashtbl.remove ri.bunch h;
      ri_delete_clause ri q;;

(***** translation from ocaml ratInput to coq RatInput *****)
let ratSingle_ht_to_RatSingle : 'a IntHashtbl.t -> (int->var) -> int list -> ratSingle_ht -> 'a coq_RatSingle =
  fun ht_cnf mk_var basis_int rsht ->
    try
    {
      new_id=rsht.new_id;
      clause_to_learn=mk_cclause mk_var rsht.clause_to_learn;
      propagate_list=clc_to_alc ht_cnf rsht.propagate_list;
      rup_proofs=List.fold_right (fun b l -> (clc_to_alc ht_cnf (try IntHashtbl.find rsht.rup_proofs b with | Not_found -> []))::l) basis_int []
    }
    with | e -> raise e
      
let ratInput_to_coq_RatInput : 'a IntHashtbl.t -> (int->var) -> ratInput -> 'a coq_RatInput =
  fun ht_cnf mk_var riht ->
    match riht with
    | None -> failwith "empty bunch"
    | Some ri ->
       let pivot = mk_literal mk_var ri.pivot in
       let remainder = IntHashtbl.fold (fun a b c -> (IntHashtbl.find ht_cnf a)::c) ri.remainder []  in
       let (basis,basis_int) = IntHashtbl.fold (fun a b (cc,ci) -> ((IntHashtbl.find ht_cnf a)::cc,a::ci)) ri.basis ([],[]) in
       let (basis,basis_int) = (List.rev basis,List.rev basis_int) in
       let bunch = IntHashtbl.fold (fun a b c -> (ratSingle_ht_to_RatSingle ht_cnf mk_var basis_int b)::c) ri.bunch [] in
       {	pivot=pivot; remainder=remainder; basis=basis; bunch=bunch; }

(***** print *****)

let print_ht_cnf =
  fun ht_cnf ->
    IntHashtbl.iter (fun a b -> Printf.printf "%d | " a) ht_cnf;
    Printf.printf "\n%!";;
	 
let print_rs : ratSingle_ht -> unit =
    fun rs ->
      Printf.printf "{ id: %d ; ctl: [ " rs.new_id;
      List.iter (fun a -> Printf.printf "%d " a) rs.clause_to_learn;
      Printf.printf "] ; pl: [  " ;
      List.iter (fun a -> Printf.printf "%d " a) rs.propagate_list;
      Printf.printf " ] ; rp: [ ";
      IntHashtbl.iter (fun a b -> Printf.printf "[ "; List.iter (fun a -> Printf.printf "%d " a) b;Printf.printf " ];";) rs.rup_proofs;
      Printf.printf " }\n%!"

let  print_ri : ratInput -> unit =
  fun ri ->
    match ri with
    | None -> Printf.printf "{\nEmpty\n}\n%!";
    |Some ri ->
      Printf.printf "{\npivot: %d\nremainder size: %d\nbasis: [ " ri.pivot (IntHashtbl.length ri.remainder);
      IntHashtbl.iter (fun a b -> Printf.printf "%d " a) ri.basis;
      Printf.printf "]\nbunch:\n";
      IntHashtbl.iter (fun a b -> print_rs b; print_newline ()) ri.bunch;
      Printf.printf "}\n%!";
   
(***********************************************************)
      
type 'a rup_res = Line of ratInput | RupClause of 'a;;

let is_RAT_line : ratLine ->  bool =
  fun (i,b,ctl,lp,nh) ->
    List.length nh != 0 || List.length lp = 0

let rec check_rup_rec =
  fun rc mk_var ht_cnf ri last->
    let (line,fin) =
      try
	OracleInput.(lratreader_curr_line (),false)
      with
      | Not_found -> ((0,false,[],[],[]),true)
      | e -> raise e
    in
    let (i,b,ctl,lp,nh) = line in
    if fin then
      match last with
      | Some c -> RupClause c
      | None -> failwith "empty LRAT file"
    else if b then
      (
	let ri = match ri with
	  |Some ri -> (match ri_delete_clause ri lp with
	                | Some ri -> Some ri
		        | None ->(* bunch was on state not_empty and is now empty *)
			   let ht_cnf_cpy = IntHashtbl.copy ht_cnf in (* TODO? *)
			   IntHashtbl.iter (fun a b -> if not(IntHashtbl.mem ri.basis a || IntHashtbl.mem ri.remainder a) then IntHashtbl.remove ht_cnf a) ht_cnf_cpy;
			   None
	              )
	  |None -> delete_clauses ht_cnf lp; ri
	in
	OracleInput.lratreader_next ();
	check_rup_rec rc mk_var ht_cnf ri last
      )
    else if is_RAT_line line then (* RAT clause *)
      let (continue,ri) = try (true,ri_add ht_cnf ri line) with |e->(false,ri)  in
      (
	if continue then
	  (OracleInput.lratreader_next ();
	   check_rup_rec rc mk_var ht_cnf ri last)
	else
	  Line ri
      )
    else if ri_check_rup_ok line ri then (* RUP clause *) 
      (
	let ci =  (rup_learn rc) (get_resolution_clauses ht_cnf lp) i (mkc mk_var ctl) in
	IntHashtbl.add ht_cnf i ci;
	(match ri with | Some ri -> IntHashtbl.add ri.remainder i () |None -> ()); (* TODO: améliorer *)
	OracleInput.lratreader_next ();
	check_rup_rec rc mk_var ht_cnf ri (Some ci)
      )
    else Line ri
      
(*
 * ___ check_rup ___
 * Process rup checking and deleting until next rat clause or end of file
 *
 * rc: coq fonction of clause learning
 * mk_var: fonction to convert int to var
 * ht_cnf: hashtable of the cnf
 *
 * return: the empty coq clause if the end of the file is reached, else a rat line
 *)
let check_rup : 'a rupLCF -> (int -> var) -> 'a IntHashtbl.t -> 'ratInput -> 'a rup_res  =
  fun rc mk_var ht_cnf ri ->
    check_rup_rec rc mk_var ht_cnf ri None

(*
 * ___ next_rat ___
 * Find the next rat clause
 *
 * rc: coq fonction of clause learning
 * c: coq cnf
 * input: oracle's data
 *
 * return: the next rat problem or the coq empty clause
 *)
let rec next_rat : (('a rupLCF * 'a list) * solver_Input) -> ('a,'a coq_RatInput) sum
  = fun ((rc,c),input) ->
    try
      (* converting the cnf: from 'a list to 'a IntHashtbl *)
      let ht_cnf = mk_learned_clauses rc c in
      (* check_rup parse lrat file and process cnf until a rat line or an empty clause (end of the proof) is found *)
      match (check_rup rc input.global.mk_var ht_cnf None) with
      | Line rio ->
	 let ri = ratInput_to_coq_RatInput ht_cnf input.global.mk_var rio in
	 Coq_inr ri
      | RupClause rclause -> Coq_inl rclause
    with
    | e -> raise e
