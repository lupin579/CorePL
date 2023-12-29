{
open Parser
}

let white = [' ' '\t']+
(* '0'-'9' are characters for here,
   beacause the inteager was taken by the string format;*)
let digit = ['0'-'9']
(* [+] denotes that int can have more than one digit,
   ['-'>] denotes that symbol [-](the negate) is optional here*)
let int = '-'? digit+
let letter = ['a'-'z' 'A'-'Z']
let id = letter+


rule read =
  parse
  | white { read lexbuf }
  | "true" { TRUE }
  | "false" { FALSE }
  | "*" { TIMES }
  | "+" { PLUS }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | "let" { LET }
  | "=" { EQUALS }
  | "<=" { LEQ }
  | "in" { IN }
  | "if" { IF }
  | "else" { ELSE }
  | "then" { THEN }
  | id { ID (Lexing.lexeme lexbuf) }
  | int { INT (int_of_string (Lexing.lexeme lexbuf)) }
  | eof { EOF }
