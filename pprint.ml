open Ast
open Format
open Proplogic

exception UnhandledConstraint of string

let rec printPolyterm chan p = match p with
 | Mono x -> Printf.fprintf chan "%s" x
 | Poly(x, p') -> Printf.fprintf chan "%s %a" x printPolyterm p' 

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
 match c with
 |Modecond (x, i) -> Printf.fprintf oc "+1 %s = %d;\n" x i
 |Eidcond  (x, i) ->Printf.fprintf oc "+1 %s =  %d;\n" x i
 |Dnfclause condlist -> let rec printorclause condlist total = 
				begin match condlist with
				|[] -> Printf.fprintf oc " >= %d;\n" total
				| (Modecond (x,i))::tail -> let total = if (i=1) then begin Printf.fprintf oc " +1 %s " x; (total +1) end
										    else begin Printf.fprintf oc " -1 %s " x; total end
								in	printorclause tail total
				| (Eidcond  (x, i))::tail ->  let total = if (i=1) then begin Printf.fprintf oc " +1 %s " x; (total +1) end
							      			else begin Printf.fprintf oc " -1 %s " x; total end
								in printorclause tail total
				| _ -> raise (UnhandledConstraint "Unsupported (hard) constraint format: dnfclause inside dnfclause")
				end
			in
			printorclause condlist 0

let printConstraints (c:constr) =
  let oc = open_out_gen [Open_creat; Open_text; Open_append] 0o640 "min.opb" in
  let _  = Constr.iter (printConstraint oc) c in
  close_out oc

(* Print single conditional constraint *)
let printSingleCondConstraint oc (a, b) =
 match a with
|Modecond (x, i1) -> begin match b with
			|Modecond(y, i2) ->
				if (i1=1)&(i2=1) then
					(* Constraint of form x = Enclave -> y = Enclave is converted to 1 -x + y >= 1 *)
					Printf.fprintf oc "-1 %s +1 %s >= 0;\n" x y
				else if (i1=1)&(i2=0) then
					(* Constraint of form x = Enclave -> y = Normal is converted to 2 -x - y >= 1 *)
					Printf.fprintf oc "-1 %s -1 %s >= -1;\n" x y
				else if (i1=0)&(i2=1) then
					(* Constraint of form x = Normal -> y = Enclave is converted to x + y >= 1 *)
					Printf.fprintf oc "+1 %s +1 %s >= 1;\n" x y
				else
					(* Constraint of form x = Normal -> y = Normal is converted to 1 +x - y >= 1 *)
					Printf.fprintf oc "+1 %s -1 %s >= 0;\n" x y

					(* Constraint of form x = Normal -> y = Normal is converted to 1 +x - y >= 1 *)
			|Eidcond  (y, i2)   -> 
				if (i1=1)&(i2=1) then
					(* Constraint of form x = Enclave -> y = 1 is converted to 1 -x + y >= 1 *)
					Printf.fprintf oc "-1 %s +1 %s >= 0;\n" x y
				else if (i1=1)&(i2=0) then
					(* Constraint of form x = Enclave -> y = 0 is converted to 2 -x - y >= 1 *)
					Printf.fprintf oc "-1 %s -1 %s >= -1;\n" x y
				else if (i1=0)&(i2=1) then
					(* Constraint of form x = Normal -> y = 1 is converted to x + y >= 1 *)
					Printf.fprintf oc "+1 %s +1 %s >= 1;\n" x y
				else
					(* Constraint of form x = Normal -> y = 0 is converted to 1 +x - y >= 1 *)
					Printf.fprintf oc "+1 %s -1 %s >= 0;\n" x y
			| _    -> raise (UnhandledConstraint "Unsupported conditional constraint format: (mu=0/1)-> (a/\ b/\ c)") 
			end
|Eidcond (x, i1) -> begin match b with
			|Modecond (y, i2) ->
				if (i1=1)&(i2=1) then
					(* Constraint of form x = 1 -> y = Enclave is converted to 1 -x + y >= 1 *)
					Printf.fprintf oc "-1 %s +1 %s >= 0;\n" x y
				else if (i1=1)&(i2=0) then
					(* Constraint of form x = 1 -> y = Normal is converted to 2 -x - y >= 1 *)
					Printf.fprintf oc "-1 %s -1 %s >= -1;\n" x y
				else if (i1=0)&(i2=1) then
					(* Constraint of form x = 0 -> y = Enclave is converted to x + y >= 1 *)
					Printf.fprintf oc "+1 %s +1 %s >= 1;\n" x y
				else
					(* Constraint of form x = 0 -> y = Normal is converted to 1 +x - y >= 1 *)
					Printf.fprintf oc "+1 %s -1 %s >= 0;\n" x y

					(* Constraint of form x = Normal -> y = Normal is converted to 1 +x - y >= 1 *)
			|Eidcond  (y, i2)   -> 
				if (i1=1)&(i2=1) then
					(* Constraint of form x = 1-> y = 1 is converted to 1 -x + y >= 1 *)
					Printf.fprintf oc "-1 %s +1 %s >= 0;\n" x y
				else if (i1=1)&(i2=0) then
					(* Constraint of form x = 1-> y = 0 is converted to 2 -x - y >= 1 *)
					Printf.fprintf oc "-1 %s -1 %s >= -1;\n" x y
				else if (i1=0)&(i2=1) then
					(* Constraint of form x = 0-> y = 1 is converted to x + y >= 1 *)
					Printf.fprintf oc "+1 %s +1 %s >= 1;\n" x y
				else
					(* Constraint of form x = 0 -> y = 0 is converted to 1 +x - y >= 1 *)
					Printf.fprintf oc "+1 %s -1 %s >= 0;\n" x y
 			|Dnfclause condlist -> let len = List.length condlist in
						let total = if i1=1 then begin
								(* Constraint of form x = 1-> y = .. /\ z = .. /\ ===> x=0 \/ (y = .. /\ z = .. /\) 
								   (x = 0 \/ y = ..) /\ (x = 0 \/ z = ..) /\ .. ===> - len x +  ... 
								*)
								Printf.fprintf oc " -%d %s " len x; 0
								end
						            else 
								begin
								(* Constraint of form x = 0-> y = .. /\ z = ..===> x=1 \/ (y=.. /\ z = ..)  
								   (x = 1 \/ y = ..) /\ (x = 1 \/ z = ..) ===> + len x +  ... 
								*)
								Printf.fprintf oc " +%d %s " len x; len
								end
						in
				let rec printorclause condlist total = begin match condlist with
					|[] -> Printf.fprintf oc " >= %d;\n" total
					|(Modecond (x,i2))::tail -> if i2=1 then begin
										Printf.fprintf oc " +1 %s " x; printorclause tail total
										end
									else 
										Printf.fprintf oc " -1 %s " x; printorclause tail (total-1)
					|(Eidcond  (x, i2))::tail ->  if i2=1 then begin Printf.fprintf oc " +1 %s " x; printorclause tail total 
											end
							      		else 
										Printf.fprintf oc " -1 %s " x; printorclause tail (total-1)
					| _ -> raise (UnhandledConstraint "Unsupported constraint format: DNFclause inside DNFclause")
				end in
				printorclause condlist total
 			end
|Dnfclause condlist ->let rec printorclause condlist total = begin match condlist with
					|[] -> total
								(* Constraint of form x = .. /\ y = .. -> z = .. ===> -x=.. \/ -y = .. \/ z = ..) *)
					|(Modecond (x,i2))::tail -> if i2=0 then begin 
										Printf.fprintf oc " +1 %s " x; printorclause tail total
										end
									else 
										begin Printf.fprintf oc " -1 %s " x; printorclause tail (total-1) end
					|(Eidcond  (x, i2))::tail ->  if i2=0 then begin Printf.fprintf oc " +1 %s " x; printorclause tail total
										end
							      else begin Printf.fprintf oc " -1 %s " x; printorclause tail (total-1) end
 					|(Dnfclause condlist)::tail -> raise (UnhandledConstraint "Unsupported constraint format: DNFclause inside DNFclause")
			end in
			let total = printorclause condlist 1 in
			begin match b with
							(* Constraint of form x = .. /\ y = .. -> z =1 .. ===> -x=.. \/ -y = .. \/ z =1 ..) *)
				|(Modecond (x,i2))-> if i2=1 then begin
									Printf.fprintf oc " +1 %s >= %d;\n" x total
									end
								else 
									begin Printf.fprintf oc " -1 %s >= %d;\n" x (total-1) end
							(* Constraint of form x = .. /\ y = .. -> z =1 .. ===> -x=.. \/ -y = .. \/ z =1 ..) *)
				|(Eidcond  (x, i2))->  if i2=1 then begin Printf.fprintf oc " +1 %s >= %d;\n " x total
									 end
							      else begin Printf.fprintf oc " -1 %s >= %d;\n" x (total-1) end
 				|(Dnfclause condlist2)-> 
							let rec printinnerorclause condlist2 = begin match condlist2 with
								|[] -> ()
								|(Modecond (x,i2))::tail -> 
											   let total = printorclause condlist 1 in
												if i2=1 then begin
													Printf.fprintf oc " +1 %s >= %d;\n" x total; printinnerorclause tail
													end
												else 
													Printf.fprintf oc " -1 %s >= %d;\n" x (total-1); printinnerorclause tail
								|(Eidcond  (x, i2))::tail ->  
											   let total = printorclause condlist 1 in
											    if i2=1 then begin 
													Printf.fprintf oc " +1 %s >= %d;\n" x total; printinnerorclause tail 
													end
											    else 
													Printf.fprintf oc " -1 %s >= %d;\n" x (total-1); printinnerorclause tail
								| _ -> raise (UnhandledConstraint "Unsupported constraint format: DNFclause inside DNFclause")
							end in
							printinnerorclause condlist2 
			end 


let printusetchannel oc u = let _ = VarSet.fold (fun el oc -> Printf.fprintf oc "%s, " el; oc )  u oc in ()


let printLabelChannel oc = function
  | Low -> Printf.fprintf oc "l"
  | High ->Printf.fprintf oc "h"
  | Erase(l, c, h) -> Printf.fprintf oc  "l ->%s  h]" c

let rec printEncTypChannel oc (lt, mumap)  = match lt with
  | (b, l) -> begin match b with
	  		| EBtInt -> Printf.fprintf oc "(int)_%a " printLabelChannel l 
 			| EBtBool -> Printf.fprintf oc "(bool)_%a " printLabelChannel l
			| EBtCond (ModeVar(x,_)) -> Printf.fprintf oc "(cond^%d)_%a " (ModeSAT.find   x mumap) printLabelChannel l
			| EBtRef(ModeVar(x,_),lt') -> Printf.fprintf oc "(%a ref^%d)_%a " printEncTypChannel (lt', mumap) (ModeSAT.find   x mumap) printLabelChannel l
			| EBtFunc(ModeVar(x,_),_,_,p, u,_,_)-> Printf.fprintf oc "func^%d@ (%a, { %a })_%a" (ModeSAT.find x mumap) printLabelChannel p printusetchannel u printLabelChannel l
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
