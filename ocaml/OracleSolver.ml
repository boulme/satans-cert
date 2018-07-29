open ImpPrelude
open SolverInterface
open SatProver
open OracleData
open SolutionParser

let rec pstring_to_string_rec =
  fun ps buff ->
    match ps with
    | Str l -> List.iter (fun c -> Buffer.add_char buff c) l;
    | CamlStr s -> String.iter (fun c -> Buffer.add_char buff c) s;
    | Concat(ps1,ps2) -> (pstring_to_string_rec ps1 buff; pstring_to_string_rec ps2 buff)

let pstring_to_string =
  fun ps ->
  let buff = Buffer.create (100) in
  pstring_to_string_rec ps buff;
  Buffer.contents buff

let run_command: oracle_data -> string -> string -> unit =
  fun input name line ->
    let ec = Sys.command line in
    (match ec with
     | 0 -> ()
     | 10 -> () (* SAT exit for SAT solvers *)
     | 20 -> () (* UNSAT exit for SAT solvers *)
     | 127 -> failwith (Printf.sprintf "Can't execute %s" name)
     | _ -> failwith (Printf.sprintf "Command %s failed" name));
    let xtime = (Unix.times()).Unix.tms_cutime in
    Printf.printf "CPU time %f\n" (xtime -. input.external_time);
    input.external_time <- xtime

let start_lrat_check: oracle_data -> solver_Answer
  = fun d ->
    OracleInput.lratreader_init d.lrat_file;
    start_certification d false;
    UNSAT_Answer

(* execute only drat-trim to make the lrat file *)
let mk_lrat: solver_Input -> string -> solver_Answer
  = fun input name ->
      let g=input.global in
      let drattrim = g.drattrim in
      let chut = " 2>&1 1>/dev/null" in
      let line = Printf.sprintf "%s %s %s -L %s %s" drattrim name g.drat_file g.lrat_file chut in
      Printf.printf "starting drat-trim...\t%!";
      run_command g "drat-trim" line;
      start_lrat_check g
      
(* execute the sat-solver to make a model, or if unsat, make the lrat file*)
let sat_solver: solver_Input -> solver_Answer
  = fun input ->
      let name = pstring_to_string input.name in
      let g=input.global in
      let satsolver = g.solver in
      match g.mode with
      | LRatCheck -> start_lrat_check g
      | LRatRecompute -> mk_lrat input name
      | _ -> ( 
	 if g.mode=Recompute || not (Sys.file_exists g.solver_outfile) then (
	    Printf.printf "starting solver...\t%!";
            let line = Printf.sprintf "%s < %s > %s" satsolver name g.solver_outfile in
            run_command g "solver" line
         );
	 let res = SolutionParser.parse (open_in g.solver_outfile) in
	 match res with
	 | Sat cm ->
	    start_certification g true;
	    SAT_Answer cm
	 | Unsat ->
            remove_on_cleaning g g.solver_outfile; (* this file is now useless *)
            mk_lrat input name
      )
