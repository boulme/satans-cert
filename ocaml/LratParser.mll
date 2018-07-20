{
let mklit i = 
  let i = int_of_string i in
  assert (i<>0);
  i

let mkindex i = 
  let i = int_of_string i in
  assert (i>0);
  i
}


let newline = '\n'
let space = [' ' '\t' '\r']+
let digit = ['0'-'9']
let sign = '-' | '+'
let integer = sign? digit+
let negative = '-' digit+
let positive = '+'? digit+

(* ([clause :int list],[resolution clauses index :int list], deleted :boolean) *)
rule clause acc = parse
| newline  { Lexing.new_line lexbuf; clause acc lexbuf }
| space { clause acc lexbuf }
| '0'  { List.rev acc }
| integer as i { clause ((mklit i)::acc) lexbuf }
| _ { failwith "Bad clauses" }

and rclauses acc n p_acc = parse
| newline { Lexing.new_line lexbuf; rclauses acc n p_acc lexbuf }
| space { rclauses acc n p_acc lexbuf }
| '0' { ((mklit n,p_acc)::acc) }
| negative as i { rclauses ((mklit n,p_acc)::acc) i [] lexbuf }
| positive as i { rclauses acc n (mklit i::p_acc) lexbuf }
| _ { failwith "Bad clauses" }

and firstrclauses pl_acc = parse
| newline { Lexing.new_line lexbuf; firstrclauses pl_acc lexbuf }
| space { firstrclauses pl_acc lexbuf }
| '0' { (pl_acc,[]) }
| negative as i { let nh = rclauses [] i [] lexbuf in (pl_acc,nh) }
| positive as i { firstrclauses (mklit i::pl_acc) lexbuf }
| _ { failwith "Bad clauses" }

and dclauses acc = parse
| newline { Lexing.new_line lexbuf; dclauses acc lexbuf }
| space { dclauses acc lexbuf }
| '0' { acc }
| positive as i { dclauses ((mklit i)::acc) lexbuf }
| _ { failwith "Bad clauses" }

and line = parse
| newline { Lexing.new_line lexbuf; line lexbuf }
| space { line lexbuf }
| '0' { let (pl,nh) = firstrclauses [] lexbuf in
        (false,[],pl,nh)
      }
| integer as i { let c = clause [(mklit i)] lexbuf in
		 let (pl,nh) = firstrclauses [] lexbuf in
	         (false,c,pl,nh)
               }
| 'd' 	{ let dc = dclauses [] lexbuf in
	  (true, [], dc, [])
	}
| _ { failwith "Bad clauses" }

and next_line = parse
| newline  { Lexing.new_line lexbuf; next_line lexbuf }
| space { next_line lexbuf }
| integer as i { let (b,c,pl,nh) = line lexbuf in
		 ((mkindex i),b,c,pl,nh)
	       }
| ['c''o'] [^'\n']* ('\n' | eof)  { Lexing.new_line lexbuf;
                               next_line lexbuf }
| eof { raise Not_found }
| _ { failwith "Bad clauses" }

 {

   let next_line lexbuf =
     next_line lexbuf

}
