open Ast
open Printf
open Pprint
open Helper
open Proplogic
open Constraints

exception PrintError
exception TranslationError of string
exception IdNotFound of string

let printkill oc (model, kj, ki') = 
  let len = List.length kj in   (* length of k and ki' should be equal *)
  let rec loop idx = 
	if (idx >= len) then 
	     ()
		(* Recall that k'' = kj \ k' *)
	else if ((ModeSAT.find (List.nth kj idx) model)=1) &&  ((ModeSAT.find (List.nth ki' idx) model)=0) then 
		let _ =	Printf.fprintf oc "kill(%d);\n" idx
		in  loop (idx+1) 
	else 
		loop (idx + 1)
  in loop 0

let printEnclaveend oc (isoutermodeenc, isprevmodeenc, iscurmodeenc, tail, model, prevk', seqk') =  match tail with
	|[] -> let _ = if (not isoutermodeenc)&&(iscurmodeenc) then
			Printf.fprintf oc ")"
		      else
			()
		in printkill oc (model, seqk', prevk')
	| TSkip(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, gamma', k')::tail
	| TSetcnd(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, gamma', k')::tail
	| TAssign (pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k')::tail
	| TDeclassify(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k')::tail
	| TUpdate(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k')::tail
	| TOut(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k')::tail
	| TIf(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, _, gamma', k')::tail
	| TWhile(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k')::tail
	| TCall(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _,  gamma', k')::tail->
		let isnextmodeenc = if (ModeSAT.find (get_mode_var mu) model)=1 then true else false in
		let _ = if (not isoutermodeenc)&&(iscurmodeenc)&&(not isnextmodeenc) then
				Printf.fprintf oc ")"
			else
				()
			in printkill oc (model, k, prevk')

let rec printEncProgram oc (model, isoutermodeenc, tstmt) = match tstmt with
| TSeq(pc, srcgamma,setu,srcgamma', s,mu,gamma, k, delta, tstmtlist, gamma', seqk') -> 
		let rec loop isoutermodeenc isprevmodeenc tstmtlist = 
			begin match tstmtlist with
			| [] -> ()
			| TSkip(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, gamma', k')::tail ->
						let iscurmodeenc = if (ModeSAT.find (get_mode_var mu) model)=1 then true else false in
						let _ = if (isoutermodeenc)||(isprevmodeenc && iscurmodeenc) || (not iscurmodeenc) then
								Printf.fprintf oc "skip;\n" 
							else (* if (not isoutermodeenc)&&(not isprevmodeenc)&&(iscurmodeenc) then *)
								Printf.fprintf oc "enclave(_, \n skip;\n " 
							in
						let _ = printEnclaveend oc (isoutermodeenc, isprevmodeenc, iscurmodeenc, tail, model, k', seqk') in
						loop isoutermodeenc iscurmodeenc tail

			| TSetcnd(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, cnd, gamma', k')::tail ->
						let iscurmodeenc = if (ModeSAT.find (get_mode_var mu) model)=1 then true else false in
						let _ = if (isoutermodeenc)||(isprevmodeenc && iscurmodeenc) || (not iscurmodeenc) then
								Printf.fprintf oc "set(%s);\n" cnd 
							else (* if (not isoutermodeenc)&&(not isprevmodeenc)&&(iscurmodeenc) then *)
								Printf.fprintf oc "enclave(_, \n set(%s);\n" cnd 
							in
						let _ = printEnclaveend oc (isoutermodeenc, isprevmodeenc, iscurmodeenc, tail, model, k', seqk') in
						loop isoutermodeenc iscurmodeenc tail

			| TAssign (pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, x, texp, gamma', k')::tail ->
						let iscurmodeenc = if (ModeSAT.find (get_mode_var mu) model)=1 then true else false in
						let _ = if (isoutermodeenc)||(isprevmodeenc && iscurmodeenc) || (not iscurmodeenc) then
								Printf.fprintf oc "%s:= %a;\n" x  printEncExp (model, texp) 
							else (* if (not isoutermodeenc)&&(not isprevmodeenc)&&(iscurmodeenc) then *)
								Printf.fprintf oc "enclave(_, \n %s:= %a;\n" x printEncExp (model, texp)  
							in
						let _ = printEnclaveend oc (isoutermodeenc, isprevmodeenc, iscurmodeenc, tail, model, k', seqk') in
						loop isoutermodeenc iscurmodeenc tail
			| TDeclassify(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, x, texp, gamma', k')::tail->
						let iscurmodeenc = if (ModeSAT.find (get_mode_var mu) model)=1 then true else false in
						let _ = if (isoutermodeenc)||(isprevmodeenc && iscurmodeenc) || (not iscurmodeenc) then
								Printf.fprintf oc "%s:= declassify(%a);\n" x  printEncExp (model, texp) 
							else (* if (not isoutermodeenc)&&(not isprevmodeenc)&&(iscurmodeenc) then *)
								Printf.fprintf oc "enclave(_, \n %s:= declassify(%a);\n" x printEncExp (model, texp)  
							in
						let _ = printEnclaveend oc (isoutermodeenc, isprevmodeenc, iscurmodeenc, tail, model, k', seqk') in
						loop isoutermodeenc iscurmodeenc tail
			| TUpdate(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, texp1, texp2, gamma', k')::tail ->
						let iscurmodeenc = if (ModeSAT.find (get_mode_var mu) model)=1 then true else false in
						let _ = if (isoutermodeenc)||(isprevmodeenc && iscurmodeenc) || (not iscurmodeenc) then
								Printf.fprintf oc "%a <- %a ;\n" printEncExp (model, texp1)  printEncExp (model, texp2) 
							else (* if (not isoutermodeenc)&&(not isprevmodeenc)&&(iscurmodeenc) then *)
								Printf.fprintf oc "enclave(_, \n %a <- %a;\n" printEncExp (model, texp1) printEncExp (model, texp2)  
							in
						let _ = printEnclaveend oc (isoutermodeenc, isprevmodeenc, iscurmodeenc, tail, model, k', seqk') in
						loop isoutermodeenc iscurmodeenc tail
			| TOut(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, ch, texp, gamma', k')::tail ->
						let iscurmodeenc = if (ModeSAT.find (get_mode_var mu) model)=1 then true else false in
						let _ = if (isoutermodeenc)||(isprevmodeenc && iscurmodeenc) || (not iscurmodeenc) then
								Printf.fprintf oc "Output %a to _ ;\n" printEncExp (model, texp)
							else (* if (not isoutermodeenc)&&(not isprevmodeenc)&&(iscurmodeenc) then *)
								Printf.fprintf oc "enclave(_, \n Output %a to _;\n" printEncExp (model, texp)
							in
						let _ = printEnclaveend oc (isoutermodeenc, isprevmodeenc, iscurmodeenc, tail, model, k', seqk') in
						loop isoutermodeenc iscurmodeenc tail
			| TIf(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, encexp, ttrue, tfalse, gamma', k')::tail -> 
						let iscurmodeenc = if (ModeSAT.find (get_mode_var mu) model)=1 then true else false in
						let _ = if (isoutermodeenc)||(isprevmodeenc && iscurmodeenc) || (not iscurmodeenc) then
							Printf.fprintf oc "If %a then \n %a \n else \n %a; \n" printeexp (model, encexp) printEncProgram  (model, iscurmodeenc, ttrue) printEncProgram (model, iscurmodeenc, tfalse) 
							else (* if (not isoutermodeenc)&&(not isprevmodeenc)&&(iscurmodeenc) then *)
							Printf.fprintf oc "enclave(_, \n If %a then \n %a \n else \n %a;\n" printeexp (model, encexp) printEncProgram  (model, iscurmodeenc, ttrue) printEncProgram (model, iscurmodeenc, tfalse) 
						in
						let _ = printEnclaveend oc (isoutermodeenc, isprevmodeenc, iscurmodeenc, tail, model, k', seqk') in
						loop isoutermodeenc iscurmodeenc tail
			| TWhile(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, encexp, tbody, gamma', k')::tail ->
						let iscurmodeenc = if (ModeSAT.find (get_mode_var mu) model)=1 then true else false in
						let _ = if (isoutermodeenc)||(isprevmodeenc && iscurmodeenc) || (not iscurmodeenc) then
								Printf.fprintf oc "while %a do \n %a \n done" printeexp (model, encexp) printEncProgram  (model, iscurmodeenc, tbody) 
							else (* if (not isoutermodeenc)&&(not isprevmodeenc)&&(iscurmodeenc) then *)
								Printf.fprintf oc "enclave(_, \n while %a do \n %a \n done" printeexp (model, encexp) printEncProgram  (model, iscurmodeenc, tbody) 
							in
							let _ = printEnclaveend oc (isoutermodeenc, isprevmodeenc, iscurmodeenc, tail, model, k', seqk') in
							loop isoutermodeenc iscurmodeenc tail
			| TCall(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, texp,  gamma', k')::tail->
						let iscurmodeenc = if (ModeSAT.find (get_mode_var mu) model)=1 then true else false in
						let _ = if (isoutermodeenc)||(isprevmodeenc && iscurmodeenc) || (not iscurmodeenc) then
								Printf.fprintf oc "call(%a);\n" printEncExp (model, texp)
							else (* if (not isoutermodeenc)&&(not isprevmodeenc)&&(iscurmodeenc) then *)
								Printf.fprintf oc "enclave(_, \n call(%a);\n" printEncExp (model, texp)
							in
						let _ = printEnclaveend oc (isoutermodeenc, isprevmodeenc, iscurmodeenc, tail, model, k', seqk') in
						loop isoutermodeenc iscurmodeenc tail
			| _ -> raise (TranslationError "Expecting non-Sequence judgment") 
			end in
		let isoutermodeenc = if (ModeSAT.find (get_mode_var mu) model)=1 then true else false in
		let isprevmodeenc  = false in
		loop isoutermodeenc isprevmodeenc tstmtlist  	
| TSkip(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, gamma', k')->
		let iscurmodeenc = if (ModeSAT.find (get_mode_var mu) model)=1 then true else false in
		if (isoutermodeenc)|| (not iscurmodeenc) then
				Printf.fprintf oc "skip\n" 
		else (* if (not isoutermodeenc)&&(not isprevmodeenc)&&(iscurmodeenc) then *)
				Printf.fprintf oc "enclave(_, \n skip)\n " 
| TSetcnd(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, cnd, gamma', k')->
			let iscurmodeenc = if (ModeSAT.find (get_mode_var mu) model)=1 then true else false in
			if (isoutermodeenc)|| (not iscurmodeenc) then
				Printf.fprintf oc "set(%s)\n" cnd 
			else (* if (not isoutermodeenc)&&(not isprevmodeenc)&&(iscurmodeenc) then *)
				Printf.fprintf oc "enclave(_, \n set(%s))\n" cnd 

| TAssign (pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, x, texp, gamma', k')->
			let iscurmodeenc = if (ModeSAT.find (get_mode_var mu) model)=1 then true else false in
			if (isoutermodeenc)|| (not iscurmodeenc) then
				Printf.fprintf oc "%s:= %a\n" x  printEncExp (model, texp) 
			else (* if (not isoutermodeenc)&&(not isprevmodeenc)&&(iscurmodeenc) then *)
				Printf.fprintf oc "enclave(_, \n %s:= %a)\n" x printEncExp (model, texp)  
| TDeclassify(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, x, texp, gamma', k')->
			let iscurmodeenc = if (ModeSAT.find (get_mode_var mu) model)=1 then true else false in
			if (isoutermodeenc)|| (not iscurmodeenc) then
				Printf.fprintf oc "%s:= declassify(%a)\n" x  printEncExp (model, texp) 
			else (* if (not isoutermodeenc)&&(not isprevmodeenc)&&(iscurmodeenc) then *)
				Printf.fprintf oc "enclave(_, \n %s:= declassify(%a))\n" x printEncExp (model, texp)  
| TUpdate(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, texp1, texp2, gamma', k')->
			let iscurmodeenc = if (ModeSAT.find (get_mode_var mu) model)=1 then true else false in
			if (isoutermodeenc)|| (not iscurmodeenc) then
				Printf.fprintf oc "%a <- %a \n" printEncExp (model, texp1)  printEncExp (model, texp2) 
			else (* if (not isoutermodeenc)&&(not isprevmodeenc)&&(iscurmodeenc) then *)
				Printf.fprintf oc "enclave(_, \n %a <- %a)\n" printEncExp (model, texp1) printEncExp (model, texp2)  
| TOut(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, ch, texp, gamma', k')->
			let iscurmodeenc = if (ModeSAT.find (get_mode_var mu) model)=1 then true else false in
			if (isoutermodeenc)|| (not iscurmodeenc) then
				Printf.fprintf oc "Output %a to _ \n" printEncExp (model, texp)
			else (* if (not isoutermodeenc)&&(not isprevmodeenc)&&(iscurmodeenc) then *)
				Printf.fprintf oc "enclave(_, \n Output %a to _)\n" printEncExp (model, texp)
| TIf(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, encexp, ttrue, tfalse, gamma', k')-> 
			let iscurmodeenc = if (ModeSAT.find (get_mode_var mu) model)=1 then true else false in
			if (isoutermodeenc)|| (not iscurmodeenc) then
				Printf.fprintf oc "If %a then \n %a \n else \n %a" printeexp (model, encexp) printEncProgram  (model, iscurmodeenc, ttrue) printEncProgram (model, iscurmodeenc, tfalse) 
			else (* if (not isoutermodeenc)&&(not isprevmodeenc)&&(iscurmodeenc) then *)
				Printf.fprintf oc "enclave(_, \n If %a then \n %a \n else \n %a)\n" printeexp (model, encexp) printEncProgram  (model, iscurmodeenc, ttrue) printEncProgram (model, iscurmodeenc, tfalse) 
| TWhile(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, encexp, tbody, gamma', k')->
			let iscurmodeenc = if (ModeSAT.find (get_mode_var mu) model)=1 then true else false in
			if (isoutermodeenc)|| (not iscurmodeenc) then
				Printf.fprintf oc "while %a do \n %a \n done \n" printeexp (model, encexp) printEncProgram  (model, iscurmodeenc, tbody) 
			else (* if (not isoutermodeenc)&&(not isprevmodeenc)&&(iscurmodeenc) then *)
				Printf.fprintf oc "enclave(_, \n while %a do \n %a \n done) \n" printeexp (model, encexp) printEncProgram  (model, iscurmodeenc, tbody) 
| TCall(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, texp,  gamma', k')->
			let iscurmodeenc = if (ModeSAT.find (get_mode_var mu) model)=1 then true else false in
			if (isoutermodeenc)|| (not iscurmodeenc) then
				Printf.fprintf oc "call(%a)\n" printEncExp (model, texp)
			else (* if (not isoutermodeenc)&&(not isprevmodeenc)&&(iscurmodeenc) then *)
				Printf.fprintf oc "enclave(_, \n call(%a))\n" printEncExp (model, texp)

and printEncExp oc (model, texp) = match texp with
|TExp(srcgamma,e,srctype, mu,gamma',delta,ence,enctype) -> printeexp oc (model, ence)
|TLamExp(srcgamma,e,srctype, mu,gamma,delta',tstmt,enctype) -> let mu' = get_translated_stmt_mode tstmt in
						begin match mu' with
						|ModeVar(x, _) ->let iscurmodeenc = if (ModeSAT.find x model) = 1 then true else false in
								Printf.fprintf oc "(lambda^%d(_,_,_,_,_).%a)" (ModeSAT.find x model) printEncProgram (model, iscurmodeenc, tstmt)
						| _ ->raise (TranslationError "Not a mode variable??!")
						end

and printeexp oc  (model, e) = match e with
  | EVar v -> Printf.fprintf oc "%s" v
  | ELam(ModeVar(x, _), pre, kpre, p, u, post, kpost, q, s) -> raise (TranslationError "Can't print function")
  | EPlus (l,r) -> Printf.fprintf oc "%a + %a" printeexp (model, l) printeexp (model, r)
  | EModulo (l,r) -> Printf.fprintf oc "%a %% %a" printeexp (model, l) printeexp (model, r)
  | EConstant n -> Printf.fprintf oc "%d" n
  | ELiteral s -> Printf.fprintf oc "%s" s
  | ETuple(f,s) -> Printf.fprintf oc "(%a, %a)" printeexp (model, f)  printeexp (model, s)
  | ETrue ->  Printf.fprintf oc "true"
  | EFalse -> Printf.fprintf oc "false"
  | EEq (l,r) -> Printf.fprintf oc "%a == %a" printeexp (model, l) printeexp (model, r)
  | ENeq (l,r) -> Printf.fprintf oc "%a != %a" printeexp (model, l) printeexp (model, r)
  | EFst e   -> Printf.fprintf oc "fst %a" printeexp (model, e)
  | ESnd e   -> Printf.fprintf oc "snd %a" printeexp (model, e)
  | ELoc (_, l) ->Printf.fprintf oc "l%d" l
  | EDeref e -> Printf.fprintf oc "*%a" printeexp (model, e)
  | EIsunset x -> Printf.fprintf oc "isunset(%s)" x
