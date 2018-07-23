(**************************************************************************)
(* This file results from modifications of file "dimacs.mll" from         *)  
(* "The Why3 Verification Platform" developed by                          *) 
(* "The Why3 Development Team"                                            *)
(*                                                                        *)
(*  See the original copyright below.                                     *)
(**************************************************************************)


(**************************************************************************)
(*                                                                        *)
(*  This file is part of Frama-C.                                         *)
(*                                                                        *)
(*  Copyright (C) 2013                                                    *)
(*    CEA (Commissariat à l'énergie atomique et aux énergies              *)
(*         alternatives)                                                  *)
(*                                                                        *)
(*  you can redistribute it and/or modify it under the terms of the GNU   *)
(*  Lesser General Public License as published by the Free Software       *)
(*  Foundation, version 2.1.                                              *)
(*                                                                        *)
(*  It is distributed in the hope that it will be useful,                 *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         *)
(*  GNU Lesser General Public License for more details.                   *)
(*                                                                        *)
(*  See the GNU Lesser General Public License version 2.1                 *)
(*  at https://www.gnu.org/licenses/lgpl-2.1.html for more details.       *)
(*                                                                        *)
(**************************************************************************)
  
{

open BinNums
open MSetPositive
  
type solution = Sat of (PositiveSet.t) | Unsat;;

let mklit i = 
   let i = int_of_string i in
   assert (i<>0);
   i

let rec int_to_positive_rec: int -> positive  = (*TODO: améliorer*)
  fun i ->
    if i <= 1 then
      Coq_xH
    else if i mod 2 == 0 then
      Coq_xO (int_to_positive_rec (i/2))
    else
      Coq_xI (int_to_positive_rec ((i-1)/2))
	
let int_to_positive: int -> positive =
  fun i ->
    int_to_positive_rec i
}

let newline = '\n'
let space = [' ' '\t' '\r']+
let digit = ['0'-'9']
let sign = '-' | '+'
let integer= sign? digit+
let positive = '+'? digit+
let sat = 's' space+ "SATISFIABLE"
let unsat = 's' space+ "UNSATISFIABLE"

rule find_s = parse
| newline  { Lexing.new_line lexbuf; find_s lexbuf }
| space    { find_s lexbuf }
| unsat { Unsat }
| sat { Sat (find_v PositiveSet.Leaf lexbuf) }
| eof { failwith "Syntax error: can't find s line" }
| _  { Lexing.new_line lexbuf; find_s lexbuf }

and find_v s = parse
| newline  { Lexing.new_line lexbuf; find_v s lexbuf }
| space    { find_v s lexbuf }
| 'v' { solution s lexbuf }
| eof { failwith "Syntax error: can't find v lines properly finished by 0" }
| _  { Lexing.new_line lexbuf; find_v s lexbuf }
    
and solution s = parse
| newline  { Lexing.new_line lexbuf; find_v s lexbuf }
| space { solution s lexbuf }
| '0'  { s }
| positive as i { solution (PositiveSet.add (int_to_positive (mklit i)) s) lexbuf }
| integer { solution s lexbuf }
| eof { failwith "Syntax error: v line ended by end-of-file (without 0)" }
| _ as c { failwith (Printf.sprintf "Syntax error: unexpected character '%c'" c) }

{

let parse cin =
  let lexbuf = Lexing.from_channel cin in
  find_s lexbuf

}
