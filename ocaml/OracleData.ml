type compute_mode = Recompute | Lazy | LRatCheck

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
  mutable external_time: float;
  to_cleanup: (string,unit) Hashtbl.t; 
}

let remove_on_cleaning (d: oracle_data) (s: string) =
  Hashtbl.replace d.to_cleanup s ()

let protect_from_cleaning (d: oracle_data) (s: string) =
  Hashtbl.remove d.to_cleanup s
    
let cleaning: oracle_data -> unit
  = fun d ->
    Hashtbl.iter (fun s _ -> try Sys.remove s with _ -> ()) d.to_cleanup

type ratLine = int*bool*(int list)*(int list)*((int*int list) list);;
