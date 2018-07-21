open Arg
open SolverInterface
open OracleData
open OracleUtils

(* TODO: is default.config really useful ? perhaps, options are simpler to deal with and sufficient ? 
let default_config_file = "default.config"
*)

(* options of the command line*)
let options: oracle_data -> (key * spec * doc) list =
  fun d ->
    [
      ("-s",String (fun s -> d.solver <- s),"[SOLVER] \t\t where SOLVER is the command to execute the solver:
\t\t\t  -solver's answer has to be on standard output (in DIMACS format)
\t\t\t  -trace proof generate by solver has to be in a file named \"proof.out\" or which named is given with -drat-file option.\n");
      ("-d",String (fun s -> d.drattrim <- s),"[DRATTRIM] \t where DRATTRIM is the path to drat-trim\n");
      ("-l",String (fun s -> d.mode <- LRatCheck; d.lrat_file <- s),"[LRAT_FILE] \t just check LRAT_FILE \n");
      ("-lrat-file",String (fun s -> d.lrat_file <- s),"[LRAT_FILE] \t name of the auxiliary LRAT_FILE \n");
      ("-drat-file",String (fun s -> d.drat_file <- s),"[DRAT_FILE] \t name of the auxiliary DRAT_FILE \n");
      ("-outfile",String (fun s -> d.solver_outfile <- s),"[DIMACS_OUT_FILE] \t name of the auxiliary DIMACS FILE OUTPUT from the sat solver \n");
      ("-f",Unit (fun () -> d.mode <- Recompute),"\t force recomputation and remove generated auxiliary files\n");
      ("-lazy",Unit (fun () -> d.mode <- Lazy),"\t skip recomputation if auxiliary file exists, and preseve these files anyway)\n");
    ]

(* action to perform just after having read the options *)
let finalize_options: oracle_data -> unit =
  fun d ->
    remove_on_cleaning d d.drat_file;
    if d.mode = Lazy && Sys.file_exists d.lrat_file then (
      d.mode <- LRatCheck
    ) else if d.mode = Recompute then (
      remove_on_cleaning d d.lrat_file;
      remove_on_cleaning d d.solver_outfile
    )

(* IDs of the clause of the cnf (1...nb_clauses) *)
let mk_problem_ids: int -> int list
  = fun nb_clauses ->
    let rec mk_problem_ids_rec =
      fun nb_clauses i acc ->
	if nb_clauses < i then
	  acc
	else
	  mk_problem_ids_rec nb_clauses (i+1) (i::acc)
    in
    mk_problem_ids_rec nb_clauses 1 []


let default_config() = {
  solver = "";
  drattrim = "drat-trim";
  solver_outfile="res.out";
  drat_file="proof.out";
  lrat_file="proof.lrat";
  mode=Recompute;
  mk_var=ImpOracles.memo_int2pos 0;
  external_time=0.0;
  to_cleanup = Hashtbl.create 10;
}
	
(* parse the command line and read the cnf *)
let parse_command_line =
  (* let (defaultsolver,defaultdrattrim) = if Sys.file_exists default_config_file then ConfigParser.parse (open_in default_config_file) else ("","drat-trim") in *)
  let d = default_config() in
  let c = options d in
  parse c (fun s -> ();) ("  usage: "^Sys.argv.(0)^" [ INPUT ] [ <OPTION> ... ]\n  where INPUT is a file in DIMACS format\n");
  finalize_options d;
  (if Array.length Sys.argv < 2 then failwith "no argument");
  let cnf_in = open_in Sys.argv.(1) in
  let (cnf,nb_var) = DimacsParser.parse(cnf_in) in
  d.mk_var<-ImpOracles.memo_int2pos nb_var;
  close_in cnf_in;
  { problem=mk_cnf d.mk_var cnf; problem_ids=mk_problem_ids (List.length cnf); name=ImpPrelude.CamlStr Sys.argv.(1); global=d }

let read_input () =
  parse_command_line
    
let print_time: solver_Input -> unit
  = fun input ->
    let my_time = (Unix.times()).Unix.tms_utime in
    let xtime = input.global.external_time in
    if xtime > 0.0 then (
      Printf.printf "* solver + drat-trim time = %f\n" xtime;    
      Printf.printf "* additional certification time = %f\n" my_time;
      Printf.printf "* overhead of additional certification time = %f%%\n" (my_time *. 100. /. xtime)
    ) else (
      Printf.printf "* total time = %f\n" my_time;
    )
      
let finalize: solver_Input -> unit
  = fun input ->
    print_time input;
    cleaning input.global

(* clrat *)
let nth_bit n i = (n lsr i) land 1;;
let clear_nth_bit n i = n land (lnot ((1 lsl i)));;

let clrat_map =
  fun x ->
    if (x land 1)==0 then x lsr 1 else -((x-1) lsr 1)
      
let clrat_next_int =
  fun cin ->
  let rec clrat_next_int_rec
      =fun cin acc i ->
	let x = input_byte cin in
	if nth_bit x 7 = 0 then acc+((clear_nth_bit x 7) lsl (i*7)) else clrat_next_int_rec cin (acc+((clear_nth_bit x 7) lsl (i*7))) (i+1)
  in
  clrat_map (clrat_next_int_rec cin 0 0)



let clrat_next_ctl
    =fun cin ->
      let rec clrat_next_ctl_rec
	  =fun cin acc ->
	    let l = clrat_next_int cin in
	    if l=0 then acc else clrat_next_ctl_rec cin (l::acc)
      in
      clrat_next_ctl_rec cin []

let clrat_read_lp_nh
    =fun cin ->
      let rec clrat_read_nh_rec
	  =fun cin n lp acc ->
	    let c = clrat_next_int cin in
	    if c=0 then (n,lp)::acc else if c>0 then clrat_read_nh_rec cin n (c::lp) acc else clrat_read_nh_rec cin c [] ((n,lp)::acc)
      in
      let rec clrat_read_lp_rec
	  =fun cin acc ->
	    let c = clrat_next_int cin in
	    if c=0 then (acc,[]) else if c>0 then clrat_read_lp_rec cin (c::acc) else (acc,clrat_read_nh_rec cin c [] [])
      in
      clrat_read_lp_rec cin []
	
let clrat_next_a_line
    =fun cin ->
      let i = clrat_next_int cin in
      let ctl = clrat_next_ctl cin in
      let (lp,nh) = clrat_read_lp_nh cin in
      (i,ctl,lp,nh)

let clrat_next_d_line
    =fun cin ->
      let dl = clrat_next_ctl cin in
      (0,[],dl,[])

(* return the next ratLine from clrat file *)
let clrat_next_line : in_channel -> ratLine 
    = fun cin ->
      let c = input_char cin in
      match c with
      | 'a' -> let (i,ctl,lp,nh) = clrat_next_a_line cin in (i,false,List.rev ctl,lp,nh)
      | 'd' -> let (i,ctl,lp,nh) = clrat_next_d_line cin in (i,true,ctl,lp,nh)
      | _ -> failwith "bad file"

(***** read lrat file *****)
	 
let lratreader_curr_line_ref : ratLine option ref = ref None
let lrat_reader_f_ref : (unit -> ratLine) ref = ref (fun () -> failwith "uninitialized lrat_reader")
  
(* return current line *)
let lratreader_curr_line : unit -> ratLine =
  fun () ->
    match !lratreader_curr_line_ref with | Some l -> l |None -> raise Not_found

(* put the next line in the buffer*)
let lratreader_next : unit -> unit =
  fun lexbuf ->
    lratreader_curr_line_ref := try Some (!lrat_reader_f_ref ()) with |Not_found|End_of_file -> None;;

(* init lrat_reader *)
let lratreader_init : string -> unit =
  fun file_name ->
    let cin = open_in file_name in
    let lexbuf = Lexing.from_channel cin  in
    lrat_reader_f_ref := (fun () -> LratParser.next_line lexbuf);
    (try
       lratreader_next ();
     with
     |_ ->(
       seek_in cin 0;
       lrat_reader_f_ref := (fun () -> clrat_next_line cin);
       lratreader_next ());
    );


