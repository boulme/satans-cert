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
    (if(ec==127) then failwith ("Can't execute "^name));
    let xtime = (Unix.times()).Unix.tms_cutime in
    Printf.printf "CPU time %f\n" (xtime -. input.external_time);
    input.external_time <- xtime
    
(* execute the sat-solver to make a model, if unsat, excecute drat-trim to make the lrat file*)
let sat_solver: solver_Input -> solver_Answer
  = fun input ->
      let name = pstring_to_string input.name in
      let g=input.global in
      let satsolver = g.solver in
      let drattrim = g.drattrim in
      if g.mode <> LRatCheck then
	(
	  Printf.printf "starting solver...\t%!";
	  if g.mode=Recompute || not (Sys.file_exists g.solver_outfile) then (
            let line = Printf.sprintf "%s < %s > %s" satsolver name g.solver_outfile in
            run_command g "solver" line
          );
	  let res = SolutionParser.parse (open_in g.solver_outfile) in
	  match res with
	  | Sat cm ->
	     Printf.printf "check sat...\n%!";
	     SAT_Answer cm
	  | Unsat ->
             remove_on_cleaning g g.solver_outfile; (* in principle, we can safely remove it ! *)
             let chut = " 2>&1 1>/dev/null" in
	     let line = Printf.sprintf "%s %s %s -L %s %s" drattrim name g.drat_file g.lrat_file chut in
	     Printf.printf "starting drat-trim...\t%!";
             run_command g "drat-trim" line;
	     OracleInput.lratreader_init (g.lrat_file);
	     UNSAT_Answer 
	)
      else
	(
	  OracleInput.lratreader_init (g.lrat_file);
	  UNSAT_Answer
	)
