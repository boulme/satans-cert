type compute_mode = Recompute | Lazy | LRatCheck | LRatRecompute

module IntHash =
struct
  type t = int
  let equal i j = i=j
  let hash i = i land max_int
end

module IntHashtbl = Hashtbl.Make(IntHash)
    
type oracle_data = {
  mutable solver: string;
  mutable drattrim: string;
  mutable solver_outfile: string; 
  mutable drat_file: string; 
  mutable lrat_file: string;
  mutable mode: compute_mode;
  mutable mk_var: int -> CnfSpec.var;
  to_cleanup: (string,unit) Hashtbl.t;
  (* below fields are only for stats *)
  mutable answer: bool option;
  mutable starting_time: float;
  mutable external_time: float;
  mutable ratbunchc: int;
  mutable ratc: int;
}

let remove_on_cleaning (d: oracle_data) (s: string) =
  Hashtbl.replace d.to_cleanup s ()

let is_removed_on_cleaning (d: oracle_data) (s: string) =
  Hashtbl.mem d.to_cleanup s

let protect_from_cleaning (d: oracle_data) (s: string) =
  Hashtbl.remove d.to_cleanup s

let start_certification (d: oracle_data) (b: bool) =
  let msg = if b then "sat" else "unsat" in
  Printf.printf "trying certification of %s..." msg;
  print_newline();
  d.answer <- Some b;
  d.starting_time <- (Unix.times()).Unix.tms_utime

let cleaning: oracle_data -> unit
  = fun d ->
    Hashtbl.iter (fun s _ -> try Sys.remove s with _ -> ()) d.to_cleanup

type ratLine = int*bool*(int list)*(int list)*((int*int list) list);;
