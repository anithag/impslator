open Ast
open Constraints
open Helper

exception MainError

let () =
  let _ =
    if (Array.length Sys.argv < 2) || (Array.length Sys.argv > 2) then
      (Format.printf "Usage: autopar <file>\n";
       exit 0) in
  let filearg = 1 in
  let file = open_in (Sys.argv.(filearg)) in
  let lexbuf = Lexing.from_channel file in
  let (gammasrc, stmt) =
    try Parser.program Lexer.token lexbuf
    with Parsing.Parse_error ->
      let pos = lexbuf.Lexing.lex_curr_p in
      Format.printf "Syntax error at line %d\n" pos.Lexing.pos_lnum;
      exit 1 in

  let mu0 = next_tvar () in (* rho = Normal *)
  let k = gen_killset () in

  (* HACK: let delta be VarLocMap instead of LocMap for quick hack *)
  let c, tstmt = (Constraints.gen_constraints_stmt Low gammasrc VarSet.empty stmt mu0 VarLocMap.empty k VarLocMap.empty) in

   ()
