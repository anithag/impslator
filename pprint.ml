open Ast
open Format

exception UnhandledConstraint of string

let rec printPolyterm chan p = match p with
 (* rho *)
 | Mono (Mode rho) -> begin match rho with
		|ModeVar (x, _) -> Printf.fprintf chan "%s" x
		| _        -> raise (UnhandledConstraint "Mode Variables should always be ModeVar")
		end
 (* bij *)
 | Mono (Eid bij) -> Printf.fprintf chan "%s" bij

 (* rho*polyterm *) 
 | Poly ((Mode rho), p') -> begin match rho with
		| ModeVar (x, _) -> Printf.fprintf chan "%s %a" x printPolyterm p'
		| _        -> raise (UnhandledConstraint "Mode Variables should always be ModeVar")
		end
 (* bij*polyterm *)
 | Poly ((Eid bij), p') -> Printf.fprintf chan "%s %a" bij printPolyterm p'

let rec printPolynomial chan fcost = 
      begin match fcost with
      | PConstant n -> Printf.fprintf chan "%d" n 
      | PMonoterm(n, p)  -> Printf.fprintf chan "%d %a" n printPolyterm p 
      | PPlus(p1, p2) -> Printf.fprintf chan "%a +%a" printPolynomial p1 printPolynomial p2
      | PMinus(p1, p2) -> Printf.fprintf chan "%a -%a" printPolynomial p1 printPolynomial p2
      | _ -> Printf.fprintf chan "\t" 	
      end

(* Print in OPB format *)
let printCost fcost max_constraints =
  let oc = open_out "min.opb" in
  let max_var = !(Helper.tvar_cell) - 1  in
     Printf.fprintf oc "* #variable= %d #constraint= %d\n" max_var max_constraints;
     Printf.fprintf oc "min: %a; \n" printPolynomial fcost;
      close_out oc

(* Print single constraint *)
let printConstraint oc c =
 begin match c with
 |Modecond (ModeVar (x, _), Enclave _) -> Printf.fprintf oc "+1 %s = 1;\n" x
 |Modecond (ModeVar (x,_), Normal) -> Printf.fprintf oc "+1 %s = 0;\n" x
 |Modecond (ModeVar (x, _), ModeVar (y, _))-> Printf.fprintf oc "+1 %s -1 %s= 0;\n" x y
 |Eidcond  (x, i) ->Printf.fprintf oc "+1 %s =  %d;\n" x i
 |Killcond  (x, i) ->Printf.fprintf oc "+1 %s =  %d;\n" x i
 |Cnfclause condlist -> let rec printorclause condlist total = begin match condlist with
				| (Modecond (ModeVar (x,_), Enclave _))::tail -> Printf.fprintf oc " +1 %s " x; printorclause tail total
				| (Modecond (ModeVar (x,_), Normal ))::tail -> Printf.fprintf oc " -1 %s " x ; printorclause tail (total-1)
				| (Modecond (ModeVar (x,_), ModeVar (y, _)))::tail -> 
						raise (UnhandledConstraint "Unsupported (hard) constraint format in cnfclause: (a \/ (rho1 = rho2))")
				| (Eidcond  (x, i))::tail -> let _ = if i=1 then Printf.fprintf oc " 1 %s " x
								          else Printf.fprintf oc " -1 %s " x
								in
							     let total' = if i=1 then total else (total-1) 
				 			     in printorclause tail total'
				|[] -> Printf.fprintf oc " >= %d;\n" total
				| _ -> raise (UnhandledConstraint "Unsupported (hard) constraint format: Cnfclause inside cnfclause")
				end in
				printorclause condlist 1
 end

let printConstraints (c:constr) =
  let oc = open_out_gen [Open_creat; Open_text; Open_append] 0o640 "min.opb" in
  let _  = Constr.iter (printConstraint oc) c in
  close_out oc

(* Print single conditional constraint *)
let printSingleCondConstraint oc (a, b) =
 match a with
|Premodecond (Enclave _, ModeVar (x,_))
|Premodecond (ModeVar (x, _), Enclave _) -> begin match b with
			|Modecond (ModeVar (y, _), Enclave _) (* Constraint of form x = Enclave -> y = Enclave is converted to 1 -x + y >= 1 *)
			|Modecond (Enclave _, ModeVar (y, _)) -> Printf.fprintf oc "-1 %s +1 %s >= 0;\n" x y

			|Modecond (ModeVar (y, _), Normal)(* Constraint of form x = Enclave -> y = Normal is converted to 2 -x - y >= 1 *)
			|Modecond (Normal, ModeVar (y,_)) -> Printf.fprintf oc "-1 %s -1 %s >= -1;\n" x y
			|Eidcond  (x, i)   -> Printf.fprintf oc " +1 %s = %d;\n " x i
			
			| _    -> raise (UnhandledConstraint "Unsupported conditional constraint format: (x=E)-> (a \/ b\/ c)") 
			end
|Premodecond (Normal, ModeVar (x,_))
|Premodecond (ModeVar (x,_), Normal) -> begin match b with
			|Modecond (ModeVar (y,_), Enclave _) (* Constraint of form x = Normal -> y = Enclave is converted to x + y >= 1 *)
			|Modecond (Enclave _ , ModeVar (y,_)) -> Printf.fprintf oc "+1 %s +1 %s >= 1;\n" x y

			|Modecond (ModeVar (y,_), Normal)(* Constraint of form x = Normal -> y = Normal is converted to 1 +x - y >= 1 *)
			|Modecond (Normal, ModeVar (y,_)) -> Printf.fprintf oc "+1 %s -1 %s >= 0;\n" x y
			|Eidcond  (x, i)   -> Printf.fprintf oc " +1 %s = %d;\n " x i
			
			| _    -> raise (UnhandledConstraint "Unsupported conditional constraint format: (x=N)-> (a \/ b\/ c)") 
			end
|Premodecond (ModeVar (x,_), ModeVar (y,_)) -> raise (UnhandledConstraint "Unsupported conditional constraint format: x=y -> ...")
|Preeidcond  ((x, ij), (y, jk)) -> begin match b  with
			|Eidcond (z, ik) -> if (ij=0) && (jk=0) && (ik=0) then
						(* constraint form: x =0 /\ y=0 -> z=0. Convert this to 1 + x + y - z >= 1 or x + y -z >=0 *)
						Printf.fprintf oc "+1 %s +1 %s -1 %s >= 0;\n" x y z
					   else if (ij=1) && (jk=0) && (ik=1) then
						(* constraint form: x =1 /\ y=0 -> z=1. Convert this to 1 - x + y + z >= 1 or -x + y +z >= 0 *)
						Printf.fprintf oc "-1 %s +1 %s +1 %s >= 0;\n" x y z
					   else
						raise (UnhandledConstraint "Unsupported conditional constraint format: (bij=1/0) /\ (bjk =1/0) -> bik = 1/0" ) 
			| _ ->		   raise (UnhandledConstraint "Unsupported conditional constraint format: (bij=1) /\ (bjk =1) -> (rho = E)" ) 
			end
|Prekillcond ((k,v1), (rho1, rho2)) -> begin match (b, rho1, rho2) with
			|Eidcond (z, v2), ModeVar (y, _), Enclave _  -> if (v1=1) && (v2=1)  then
							(* kill constraint k = 1 /\ y = 1 -> z =1. Equivalent to -k -y +z>=-1 *)
								Printf.fprintf oc "-1 %s  -1 %s +1 %s >= 0;\n" k y z 
					    		else
								raise (UnhandledConstraint "Unsupported conditional constraint format: k=0/1 /\ rho =0/1 -> b=0/1" )

			| _ ->		   		raise (UnhandledConstraint "Unsupported conditional constraint format: k=0/1 /\ rho =0/1 -> b=0/1" )
			end
|Prekillexitcond ((Enclave _, ModeVar (x,_)),(Normal, ModeVar (y,_))) 
|Prekillexitcond ((ModeVar (x,_), Enclave _), (ModeVar (y,_), Normal)) -> begin match b with
			|Killcond (k, i) -> if i = 1 then
						 (* x =1 /\ y =0 -> k = 1. Equivalent to -x + y + k >=0 *)
						Printf.fprintf oc "-1 %s +1 %s +1 %s >= 0;\n" x y k
					    else
						raise (UnhandledConstraint "Unsupported conditional constraint format: rho=0/1 /\ rho =0/1 -> k=0/1" )
			|_ ->	raise (UnhandledConstraint "Unsupported conditional constraint format: rho=0/1 /\ rho =0/1 -> k=0/1" )
			end
let printusetchannel oc u = let _ = VarSet.fold (fun el oc -> Printf.fprintf oc "%s, " el; oc )  u oc in ()


let printLabelChannel oc = function
  | Low -> Printf.fprintf oc "l"
  | High ->Printf.fprintf oc "h"
  | Erase(l, c, h) -> Printf.fprintf oc  "l ->%s  h]" c

let rec printEncTypChannel oc (lt, rhomap)  = match lt with
  | (b, l) -> begin match b with
	  		| EBtInt -> Printf.fprintf oc "(int)_%a " printLabelChannel l 
 			| EBtBool -> Printf.fprintf oc "(bool)_%a " printLabelChannel l
			| EBtCond m -> Printf.fprintf oc "(cond^%d)_%a " (ModeSAT.find  (Mode m) rhomap) printLabelChannel l
			| EBtRef(m,lt') -> Printf.fprintf oc "(%a ref^%d)_%a " printEncTypChannel (lt', rhomap) (ModeSAT.find  (Mode m) rhomap) printLabelChannel l
			| EBtFunc(m,_,p, u,_)-> Printf.fprintf oc "func^%d@ (%a, { %a })_%a" (ModeSAT.find (Mode m) rhomap) printLabelChannel p printusetchannel u printLabelChannel l
			end
  | _ -> raise Not_found


let printCondConstraints (c:constr2) =
  let oc = open_out_gen [Open_creat; Open_text; Open_append] 0o640 "min.opb" in
  let _  = Constr2.iter (printSingleCondConstraint oc) c in
  close_out oc

let printMode' ppf = function
 | (ModeVar (x,_), ModeVar(y,_)) -> printf "@[%s, %s @]" x y
 | _  -> raise Not_found
 

let print_keyval key value = printf "@[%s : %a \n @]" key printMode' value
let printEidMap' ppf m = EnclaveidMap.iter print_keyval m
let printEidMap m = 
   printEidMap' Format.std_formatter m
