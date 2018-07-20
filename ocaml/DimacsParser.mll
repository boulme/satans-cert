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

let mklit i = 
   let i = int_of_string i in
   assert (i<>0);
   i

}

let newline = '\n'
let space = [' ' '\t' '\r']+
let digit = ['0'-'9']
let sign = '-' | '+'
let integer = sign? digit+
  
rule find_header = parse
| newline  { Lexing.new_line lexbuf; find_header lexbuf }
| space    { find_header lexbuf }
| 'p'
    space+ "cnf"
    space+ (digit+ as nb_var)
    space+ (digit+ as nb_cls) { int_of_string nb_var,
                                int_of_string nb_cls }
| 'c' [^'\n']* '\n'  { Lexing.new_line lexbuf; find_header lexbuf }
| _
      { failwith "Can't find header" }

and clause acc = parse
| newline  { Lexing.new_line lexbuf; clause acc lexbuf }
| space { clause acc lexbuf }
| '0'  { List.rev acc }
| integer as i { clause ((mklit i)::acc) lexbuf }
| _ { failwith "Bad clause" }

and file cnf = parse
| newline  { Lexing.new_line lexbuf; file cnf lexbuf }
| space { file cnf lexbuf }
| '0'  { file ([]::cnf) lexbuf }
| integer as i { let l = clause [mklit i] lexbuf in
                 file (l::cnf) lexbuf
               }
| 'c' [^'\n']* ('\n' | eof)  { Lexing.new_line lexbuf;
                               file cnf lexbuf }
| eof { List.rev cnf }
| _ { failwith "Bad clauses" }

{

let parse cin =
  let lexbuf = Lexing.from_channel cin in
  let nb_var, _ = find_header lexbuf in
  (file [] lexbuf,nb_var)

}
