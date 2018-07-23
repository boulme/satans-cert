(* Warning 

This oracle assumes the following extraction directives:
  "Require Import ExtrOcamlString."

*)

open ImpPrelude
open BinNums
open Datatypes

(* two auxiliary functions, for efficient mapping of "int" to "BinNums.positive" *)
exception Overflow
  
let aux_add: ('a, 'b) Hashtbl.t -> 'b Queue.t -> 'a -> 'b -> unit
  = fun t q i p ->
    if i < 1 then (* protection against wrap around *)
      raise Overflow;
    Queue.add p q;
    Hashtbl.add t i p

let memo_int2pos: int -> int -> BinNums.positive
  = fun n ->
    (* init of the Hashtbl *)
    let n = max n 1 in
    let t = Hashtbl.create n in
    let q = Queue.create () in
    aux_add t q 1 BinNums.Coq_xH ;
    for i = 1 to (n-1)/2 do
      let last = Queue.take q in
      let ni = 2*i in
      aux_add t q ni (BinNums.Coq_xO last);
      aux_add t q (ni+1) (BinNums.Coq_xI last)
    done;
    if n mod 2 = 0 then (
      let last = Queue.take q in
      Hashtbl.add t n (BinNums.Coq_xO last)
    );
    (* memoized translation of i *)
    let rec find i =
      try
        (* Printf.printf "-> %d\n" i; *)
        Hashtbl.find t i
      with Not_found ->
        (* Printf.printf "<- %d\n" i; *)
        if i <= 0 then
          invalid_arg "non-positive integer"
        else
          let p = find (i/2) in
          let pi = if i mod 2 = 0 then BinNums.Coq_xO p else BinNums.Coq_xI p in
          Hashtbl.add t i pi;
          pi
     in find;;
           
  
let string_coq2caml: char list -> string
  = fun l ->
    let buf = Buffer.create (List.length l) in
    List.iter (fun c -> Buffer.add_char buf c) l;
    Buffer.contents buf;;

let new_exit_observer: (unit -> unit) -> (unit -> unit) ref
  = fun f ->
    let o = ref f in 
    at_exit (fun () -> !o());
    o;;

let set_exit_observer: (unit -> unit) ref * (unit -> unit) -> unit
  = fun (r, f) -> r := f

let rec print: pstring -> unit
  = fun ps ->
    match ps with
    | Str l -> List.iter print_char l
    | CamlStr s -> print_string s
    | Concat(ps1,ps2) -> (print ps1; print ps2);;

let println: pstring -> unit
  = fun l -> print l; print_newline()

exception ImpureFail of pstring;;

let exn2string: exn -> pstring
  = fun e -> CamlStr (Printexc.to_string e)

let fail: pstring -> 'a
  = fun s -> raise (ImpureFail s);;

let try_with_fail: (unit -> 'a) * (pstring -> exn -> 'a) -> 'a
  = fun (k1, k2) ->
    try
      k1()
    with
    | (ImpureFail s) as e -> k2 s e

let try_with_any: (unit -> 'a) * (exn -> 'a) -> 'a
  = fun (k1, k2) ->
    try
      k1()
    with
    | e -> k2 e

(** GENERIC ITERATIVE LOOP **) 

(* a simple version of loop *)
let simple_loop: ('a * ('a -> ('a, 'b) sum)) -> 'b
  = fun (a0, f) ->
    let rec iter: 'a -> 'b
      = fun a ->
        match f a with
        | Coq_inl a' -> iter a'
        | Coq_inr b -> b
    in
    iter a0;;

(* loop from while *)
let while_loop: ('a * ('a -> ('a, 'b) sum)) -> 'b
  = fun (a0, f) ->
    let s = ref (f a0) in
    while (match !s with Coq_inl _ -> true | _ -> false) do
      match !s with
      | Coq_inl a -> s:=f a
      | _ -> assert false
    done;
    match !s with
    | Coq_inr b -> b
    | _ -> assert false;;

let loop = simple_loop


(** GENERIC FIXPOINTS **)
  
let std_rec (recf: ('a -> 'b ) -> 'a -> 'b): 'a -> 'b =
  let rec f x = recf f x in
  f

let memo_rec (recf: ('a -> 'b ) -> 'a -> 'b): 'a -> 'b  =
  let memo = Hashtbl.create 10 in
  let rec f x =
    try
      Hashtbl.find memo x
    with
      Not_found ->
        let r = recf f x in
        Hashtbl.replace memo x r;
        r
  in f

let bare_rec (recf: ('a -> 'b ) -> 'a -> 'b): 'a -> 'b  =
  let fix = ref (fun x -> failwith "init") in
  fix := (fun x -> recf !fix x);
  !fix;;
  
let buggy_rec (recf: ('a -> 'b ) -> 'a -> 'b): 'a -> 'b =
  let memo = ref None in
  let rec f x =
    match !memo with
    | Some y -> y
    | None ->
       let r = recf f x in
       memo := Some r;
       r
  in f

let xrec_mode = ref MemoRec

let xrec_set_option : recMode -> unit
= fun m -> xrec_mode := m

let xrec : (('a -> 'b ) -> 'a -> 'b ) -> ('a -> 'b )
  = fun recf ->
    match !xrec_mode with
    | StdRec -> std_rec recf
    | MemoRec -> memo_rec recf
    | BareRec -> bare_rec recf
    | BuggyRec -> buggy_rec recf


(** MISC **)

let rec posTr: BinNums.positive -> int
= function
  | BinNums.Coq_xH -> 1
  | BinNums.Coq_xO p -> (posTr p)*2
  | BinNums.Coq_xI p -> (posTr p)*2+1;;

let zTr: BinNums.coq_Z -> int
= function
  | BinNums.Z0 -> 0
  | BinNums.Zpos p -> posTr p
  | BinNums.Zneg p -> - (posTr p)

let ten = BinNums.Zpos (BinNums.Coq_xO (BinNums.Coq_xI (BinNums.Coq_xO BinNums.Coq_xH)))

let rec string_of_pos (p:BinNums.positive) (acc: pstring): pstring
= let (q,r) = BinIntDef.Z.pos_div_eucl p ten in       
  let acc0 = Concat (CamlStr (string_of_int (zTr r)), acc) in    
  match q with
  | BinNums.Z0 -> acc0
  | BinNums.Zpos p0 -> string_of_pos p0 acc0
  | _ -> assert false

let string_of_Z_debug: BinNums.coq_Z -> pstring
= fun p -> CamlStr (string_of_int (zTr p))

let string_of_Z: BinNums.coq_Z -> pstring
= function
  | BinNums.Z0 -> CamlStr "0"
  | BinNums.Zpos p -> string_of_pos p (CamlStr "")
  | BinNums.Zneg p -> Concat (CamlStr "-", string_of_pos p (CamlStr ""))

let timer ((f:'a -> 'b), (x:'a)) : 'b =
  Gc.compact();
  let itime = (Unix.times()).Unix.tms_utime in
  let r = f x in
  let rt = (Unix.times()).Unix.tms_utime -. itime in
  Printf.printf "time = %f\n" rt;
  r
