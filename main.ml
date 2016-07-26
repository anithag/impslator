open Ast
open Constraints
open Helper
open Proplogic
open Convertconstraints
open Pprint
open Printf
open Util
open Translate
open Optimize


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
  let usedenclave = gen_killset ()  in
  
  (* HACK: let delta be VarLocMap instead of LocMap for quick hack *)
  let (c0, delta, genc) = (Constraints.translategamma gammasrc) in
  let c, tstmt = (Constraints.gen_constraints_stmt Low gammasrc VarSet.empty stmt mu0 genc k delta true usedenclave) in

  (* All killed enclaves should be disjoint *)
  let killc = gen_constraints_killsets tstmt c in

  let c = TConstraints.union killc c0  in

  (* μ0 = N *)
  let c' = TConstraints.add (ModeisN (mu0,0)) c in

  let c'' = TConstraints.add (Enclaveid mu0) c' in

  (* k = Ø *)
  let c''' = TConstraints.add (Killempty k) c' in


  let mulist = get_enclaves_of_confidential_locations genc in

  (* usedenclave[i] = 1 <-> \/ mulist[i] = 1 *)
  let usedEncConstraints = TConstraints.add (UsedEnclave (usedenclave, mulist)) c''' in
 
  (* Convert translation constraints into proposition logic *)
  let (c1, c2) = Convertconstraints.convertconstraints (Constr.empty) (Constr2.empty) usedEncConstraints in
  
  (* No optimization for now *)
  let mu0var = get_mode_var mu0 in
  let tcbcost =	gen_tcb_objective (PMonoterm (0, (Mono mu0var))) tstmt in
  (* let totalc = tcbcost in
   *)
  let totalc =	gen_critical_window_objective  tcbcost tstmt in 

  let condconstr_num = Helper.countCondConstraints c2 in
  let _ = Pprint.printCost totalc ((Constr.cardinal c1) + condconstr_num) in

  (* Convert proposition logic formulae to pseudo Boolean Constraints *)
  let _ = Pprint.printConstraints c1 in
  let _ = Pprint.printCondConstraints c2 in
  
  let _ = Format.printf "Calling Solver \n" in
  (* Call Solver and get output *) 
   (* let out= (read_process "java -jar /Users/anithagollamudi/research/solvers/sat4j/sat4j-pb.jar min.opb" ) in *) 
  let out= (read_process "/Users/anithagollamudi/research/solvers/toysolver-master/dist/build/toysat/toysat --pb min.opb") in 
  let _ = Printf.printf "%s" out in

  let model = Util.extractsatmodel out in
  let oc = open_out "output.txt" in
  let _ = Printf.fprintf oc "\n (# Enclave Type Declarations #)\n" in
  let _ = Translate.printEncLocTypes oc (model, genc) in
  let _ = Printf.fprintf oc "\n (# Enclave Program #)\n" in
  
  let _ = Translate.printEncProgram oc (model, false, tstmt) in
   ()
