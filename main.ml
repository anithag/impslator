open Ast
open Constraints
open Helper
open Proplogic
open Convertconstraints
open Pprint
open Printf
open Util
open Translate


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
 
  (* Convert translation constraints into proposition logic *)
  let (c1, c2) = Convertconstraints.convertconstraints (Constr.empty) (Constr2.empty) c in
  
  (* No optimization for now *)
  let mu0var = get_mode_var mu0 in
  let totalc = 	PPlus (PMonoterm (0, (Mono mu0var)), PMonoterm (0, (Mono mu0var))) in 

  let condconstr_num = Helper.countCondConstraints c2 in
  let _ = Pprint.printCost totalc ((Constr.cardinal c1) + condconstr_num) in

  (* Convert proposition logic formulae to pseudo Boolean Constraints *)
  let _ = Pprint.printConstraints c1 in
  let _ = Pprint.printCondConstraints c2 in
  
  let _ = Format.printf "Calling Solver \n" in
  (* Call Solver and get output *) 
  (* let out= (read_process "java -jar /Users/anithagollamudi/research/solvers/sat4j/sat4j-pb.jar min.opb" ) in  *)
  let out= (read_process "/Users/anithagollamudi/research/solvers/toysolver-master/dist/build/toysat/toysat --pb min.opb") in
  let _ = Printf.printf "%s" out in

  let model = Util.extractsatmodel out in
  let oc = open_out "output.txt" in
  let _ = Translate.printEncProgram oc (model, false, tstmt) in
   ()
