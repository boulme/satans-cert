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
  
let newline = '\n'
let space = [' ' '\t' '\r']+
let solver = "-s"
let drattrim = "-d"

rule find_id s d = parse
| newline  { Lexing.new_line lexbuf; find_id s d lexbuf }
| space    { find_id s d lexbuf }
| solver { line s lexbuf; find_id s d lexbuf }
| drattrim { line d lexbuf; find_id s d lexbuf }
| eof {  }
| _  { Lexing.new_line lexbuf; find_id s d lexbuf}

and line b = parse
| newline  { Lexing.new_line lexbuf; }
| eof {  }
| _  as c { Buffer.add_char b c; line b lexbuf; }

{

let parse cin =
  let lexbuf = Lexing.from_channel cin in
  let solver = Buffer.create(100) in
  let drattrim = Buffer.create(100) in
  find_id solver drattrim lexbuf;
  (Buffer.contents solver, Buffer.contents drattrim)

}
