{
open Parser
open Printf
exception Eof
exception Err
let incline lexbuf =
  let pos = lexbuf.Lexing.lex_curr_p in
  lexbuf.Lexing.lex_curr_p <- { pos with
    Lexing.pos_lnum = pos.Lexing.pos_lnum + 1;
    Lexing.pos_bol = pos.Lexing.pos_cnum;
  }
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

| _ as c  { 
            let pos = lexbuf.Lexing.lex_curr_p in
            printf "Error at line %d\n" pos.Lexing.pos_lnum;
            printf "Unrecognized character: [%c]\n" c;
            exit 1 
          }
