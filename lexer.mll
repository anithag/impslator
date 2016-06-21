{
open Parser
open Printf
exception Eof
exception Err
let brace_depth = ref 0
and comment_depth = ref 0
let incline lexbuf =
  let pos = lexbuf.Lexing.lex_curr_p in
  lexbuf.Lexing.lex_curr_p <- { pos with
    Lexing.pos_lnum = pos.Lexing.pos_lnum + 1;
    Lexing.pos_bol = pos.Lexing.pos_cnum;
  }

exception Lexical_error of string * string * int * int

let handle_lexical_error fn lexbuf =
  let p = Lexing.lexeme_start_p lexbuf in
  let line = p.Lexing.pos_lnum
  and column = p.Lexing.pos_cnum - p.Lexing.pos_bol + 1
  and file = p.Lexing.pos_fname
  in
  try
    fn lexbuf
  with Lexical_error (msg, "", 0, 0) ->
    raise(Lexical_error(msg, file, line, column))

}

let digit = ['0'-'9']
let id = ['a'-'z'] ['a'-'z' '0'-'9' '-']*
let ws = [' ' '\t']
let location =['l']['0'-'9']* 
let literal = ['"']['a'-'z' '0'-'9' '-']*['"']
let array  = ['[']['0'-'9']*[']']

rule token = parse
| ws      { token lexbuf }
| '\n'    { incline lexbuf; token lexbuf }
| "=="     { EQUALS }
| "!="     { NEQUALS }
| "+"     { PLUS }
| "%"     { MODULO  }
| "<"	  { LESSTHAN}
| "("     { LPAREN }
| ")"     { RPAREN }
| "{"	  {LCURLY}
| "}"     {RCURLY}
| "["	  {LSQBR}
| "]"	  {RSQBR}
| "."     { DOT }
| ","     {COMMA}
| ";"     { SEQ }
| ":="    { ASSIGN }
| ":"     {COLON}
| "true"  { TRUE } 
| "false" { FALSE }
| "isunset" {ISUNSET}
| "fst"    {FST}
| "snd"	   {SND}
| "skip"  { SKIP }
| "if"    { IF }
| "then"  { THEN }
| "else"  { ELSE }
| "fi"    {ENDIF}
| "lambda" { LAMBDA }
| "declassify" {DECLASSIFY}
| "<-"    { UPDATE }
| "output" {OUTPUT}
| "while" { WHILE}
| "do"    { DO }
| "end"   {END}
| "call"  {CALL}
| "set"   {SET}
| "int"   { INT } 
| "bool"  { BOOL } 
| "string"  { STRING } 
| "cond"  {COND}
| "func"  {FUNC}
| "ref"   {REF}
| "_"	  {UNDERSCORE}
| "low"	  {LOW}
| "high"  {HIGH}
| "top"   {TOP}
| "L"|"H" as channel {CHANNEL(channel)}
| "~"    { ERASE}
| location as l {LOC(int_of_string (String.sub l 1 ((String.length l)-1)))}
(* | array as arr {ARRAY(int_of_string (String.sub arr 1 ((String.length arr)-2)))} *)
| literal as strlit {LITERAL(strlit)}
| id as v { VAR(v) }
| "*"     { DEREF }
| digit+ as n  { INTEGER(int_of_string n) }
| eof     { EOF }
| "(#"
      { comment_depth := 1;
        handle_lexical_error comment lexbuf;
        token lexbuf }
| _ as c  { 
            let pos = lexbuf.Lexing.lex_curr_p in
            printf "Error at line %d\n" pos.Lexing.pos_lnum;
            printf "Unrecognized character: [%c]\n" c;
            exit 1 
          }

and comment = parse
    "(#"
    { incr comment_depth; comment lexbuf }
  | "#)"
    { decr comment_depth;
      if !comment_depth = 0 then () else comment lexbuf }
  | "'"
    { skip_char lexbuf ;
     comment lexbuf }
  | eof
    { raise(Lexical_error("unterminated comment", "", 0, 0)) }
  | _
    { comment lexbuf }

and skip_char = parse
  | [^ '\\' '\''] "'" (* regular character *)
(* one character and numeric escape sequences *)
  | '\\' _ "'"
  | '\\' ['0'-'9'] ['0'-'9'] ['0'-'9'] "'"
  | '\\' 'x' ['0'-'9' 'a'-'f' 'A'-'F'] ['0'-'9' 'a'-'f' 'A'-'F'] "'"
     {()}
(* Perilous *)
  | "" {()}

