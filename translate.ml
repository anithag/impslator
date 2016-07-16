open Ast
open Printf
open Pprint
open Helper
open Proplogic
open Constraints

exception PrintError
exception TranslationError of string
exception IdNotFound of string

let rec printPolicy oc p = match p with
 |Low -> Printf.fprintf oc "low"
 |High -> Printf.fprintf oc "high"
 |Erase (p1, x, p2) -> Printf.fprintf oc "%a /%s %a" printPolicy p1 x printPolicy p2
 |Top   -> Printf.fprintf oc "T"

let get_enclave_id model mu = begin match mu with
    |ModeVar (mu1, li) -> 
		        let iscurmodeenc = if (ModeSAT.find mu1 model) = 1 then true else false in
			let rec loop li id = begin match li with
			|[] -> raise (TranslationError "No enclave id found")
			|xs::tail -> (* Only one xs should be 1 *) 
				    if (ModeSAT.find xs model) = 1 then (id+1) else
					loop tail (id+1) 
			end in
			if iscurmodeenc then loop li 0 else -1

    |_ -> raise (TranslationError "No enclave id found")
    end
let printArrayLoc oc li = 
  let rec loop li = begin match li with
   |[] -> ()
   |xs::tail -> let _ = Printf.fprintf oc "l%d," xs in
		loop tail
  end in loop li

let printkill oc (model, k'') = 
  let len = List.length k'' in 
  let rec loop idx = 
	if (idx >= len) then 
	     ()
	else if ((ModeSAT.find (List.nth k'' idx) model)=1) then
		let _ =	Printf.fprintf oc "kill(%d);\n" (idx+1)
		in  loop (idx+1) 
	else 
		loop (idx + 1)
  in loop 0

let printEnclaveend oc (isoutermodeenc, isprevmodeenc, iscurmodeenc, curencid, tail, model, k'') =  match tail with
	|[] -> let _ = if (not isoutermodeenc)&&(iscurmodeenc) then
			Printf.fprintf oc ");\n"
		      else
			()
		in printkill oc (model, k'')
	| (TSkip(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, gamma', k'), _)::tail
	| (TSetcnd(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, gamma', k'), _)::tail
	| (TAssign (pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k'), _)::tail
	| (TDeclassify(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k'), _)::tail
	| (TUpdate(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k'), _)::tail
	| (TOut(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k'), _)::tail
	| (TIf(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, _, gamma', k'), _)::tail
	| (TWhile(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k'), _)::tail
	| (TCall(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _,  gamma', k'), _)::tail->
		let isnextmodeenc = if (ModeSAT.find (get_mode_var mu) model)=1 then true else false in
		let nextencid	 = if isnextmodeenc then
						get_enclave_id model mu 
				   else
						-1 
				   in
		let isnextencsame = if (curencid = nextencid) then true else false in
		let _ 		 = if (not isoutermodeenc)&&(iscurmodeenc)&&(not isnextmodeenc) || (iscurmodeenc && isnextmodeenc && not isnextencsame) then
					Printf.fprintf oc ");\n"
				   else
					()
				in printkill oc (model, k'')


let rec printEncProgram oc (model, isoutermodeenc, tstmt) = match tstmt with
| TSeq(pc, srcgamma,setu,srcgamma', s,mu,gamma, k, delta, tstmtlist, gamma', seqk') -> 
		let rec loop isoutermodeenc isprevmodeenc prevencid tstmtlist = 
			begin match tstmtlist with
			| [] -> ()
			| (TSkip(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, gamma', k'), k'')::tail ->
						let iscurmodeenc = if (ModeSAT.find (get_mode_var mu) model)=1 then true else false in
						let curencid	 = if iscurmodeenc then
										get_enclave_id model mu 
								   else
										-1 
								   in
						let isprevencsame = if (curencid = prevencid) then true else false in
						let _ = if (isoutermodeenc)||(isprevmodeenc && iscurmodeenc && isprevencsame) || (not iscurmodeenc) ||
										(not isoutermodeenc && isprevmodeenc && not iscurmodeenc)	 then
								Printf.fprintf oc "skip;\n" 
							else 
								Printf.fprintf oc "enclave(%d, \n skip;\n " curencid 
							in
						let _ = printEnclaveend oc (isoutermodeenc, isprevmodeenc, iscurmodeenc, curencid, tail, model, k'') in
						loop isoutermodeenc iscurmodeenc curencid tail
			| (TSetcnd(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, cnd, gamma', k'), k'')::tail ->
						let iscurmodeenc = if (ModeSAT.find (get_mode_var mu) model)=1 then true else false in
						let curencid	 = if iscurmodeenc then
										get_enclave_id model mu 
								   else
										-1 
								   in
						let isprevencsame = if (curencid = prevencid) then true else false in
						let _ = if (isoutermodeenc)||(isprevmodeenc && iscurmodeenc && isprevencsame ) || (not iscurmodeenc) || 
										(not isoutermodeenc && isprevmodeenc && not iscurmodeenc)	 then
								Printf.fprintf oc "set(%s);\n" cnd 
							else if (not isoutermodeenc && isprevmodeenc && not iscurmodeenc) then
								Printf.fprintf oc ");\n set(%s);\n" cnd 
							else (* if (not isoutermodeenc)&&(not isprevmodeenc)&&(iscurmodeenc) then *)
								Printf.fprintf oc "enclave(%d, \n set(%s);\n" curencid cnd 
							in
						let _ = printEnclaveend oc (isoutermodeenc, isprevmodeenc, iscurmodeenc, curencid,tail, model, k'') in
						loop isoutermodeenc iscurmodeenc curencid tail

			| (TAssign (pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, x, texp, gamma', k'),k'')::tail ->
						let iscurmodeenc = if (ModeSAT.find (get_mode_var mu) model)=1 then true else false in
						let curencid	 = if iscurmodeenc then
										get_enclave_id model mu 
								   else
										-1 
								   in
						let isprevencsame = if (curencid = prevencid) then true else false in
						let _ = if (isoutermodeenc)||(isprevmodeenc && iscurmodeenc && isprevencsame) || (not iscurmodeenc) || 
										(not isoutermodeenc && isprevmodeenc && not iscurmodeenc)	 then
								Printf.fprintf oc "%s:= %a;\n" x  printEncExp (model, texp) 
							else if (not isoutermodeenc && isprevmodeenc && not iscurmodeenc) then
								Printf.fprintf oc "); \n %s:= %a;\n" x  printEncExp (model, texp) 
							else 
								Printf.fprintf oc "enclave(%d, \n %s:= %a;\n" curencid x printEncExp (model, texp)  
							in
						let _ = printEnclaveend oc (isoutermodeenc, isprevmodeenc, iscurmodeenc, curencid, tail, model, k'') in
						loop isoutermodeenc iscurmodeenc curencid tail
			| (TDeclassify(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, x, texp, gamma', k'),k'')::tail->
						let iscurmodeenc = if (ModeSAT.find (get_mode_var mu) model)=1 then true else false in
						let curencid	 = if iscurmodeenc then
										get_enclave_id model mu 
								   else
										-1 
								   in
						let isprevencsame = if (curencid = prevencid) then true else false in
						let _ = if (isoutermodeenc)||(isprevmodeenc && iscurmodeenc && isprevencsame) || (not iscurmodeenc) || 
										(not isoutermodeenc && isprevmodeenc && not iscurmodeenc)	 then
								Printf.fprintf oc "%s:= declassify(%a);\n" x  printEncExp (model, texp) 
							else if (not isoutermodeenc && isprevmodeenc && not iscurmodeenc) then
								Printf.fprintf oc ");\n %s:= declassify(%a);\n" x  printEncExp (model, texp) 
							else 
								Printf.fprintf oc "enclave(%d, \n %s:= declassify(%a);\n" curencid  x printEncExp (model, texp)  
							in
						let _ = printEnclaveend oc (isoutermodeenc, isprevmodeenc, iscurmodeenc, curencid, tail, model, k'') in
						loop isoutermodeenc iscurmodeenc curencid tail
			| (TUpdate(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, texp1, texp2, gamma', k'), k'')::tail ->
						let iscurmodeenc = if (ModeSAT.find (get_mode_var mu) model)=1 then true else false in
						let curencid	 = if iscurmodeenc then
										get_enclave_id model mu 
								   else
										-1 
								   in
						let isprevencsame = if (curencid = prevencid) then true else false in
						let _ = if (isoutermodeenc)||(isprevmodeenc && iscurmodeenc && isprevencsame) || (not iscurmodeenc) || 
										(not isoutermodeenc && isprevmodeenc && not iscurmodeenc)	 then
								Printf.fprintf oc "%a <- %a ;\n" printEncExp (model, texp1)  printEncExp (model, texp2) 
							else if (not isoutermodeenc && isprevmodeenc && not iscurmodeenc) then
								Printf.fprintf oc ");\n %a <- %a ;\n" printEncExp (model, texp1)  printEncExp (model, texp2) 
							else 
								Printf.fprintf oc "enclave(%d, \n %a <- %a;\n" curencid printEncExp (model, texp1) printEncExp (model, texp2)  
							in
						let _ = printEnclaveend oc (isoutermodeenc, isprevmodeenc, iscurmodeenc, curencid, tail, model, k'') in
						loop isoutermodeenc iscurmodeenc curencid tail
			| (TOut(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, ch, texp, gamma', k'),k'')::tail ->
						let iscurmodeenc = if (ModeSAT.find (get_mode_var mu) model)=1 then true else false in
						let curencid	 = if iscurmodeenc then
										get_enclave_id model mu 
								   else
										-1 
								   in
						let isprevencsame = if (curencid = prevencid) then true else false in
						let _ = if (isoutermodeenc)||(isprevmodeenc && iscurmodeenc && isprevencsame) || (not iscurmodeenc) || 
										(not isoutermodeenc && isprevmodeenc && not iscurmodeenc)	 then
								Printf.fprintf oc "Output %a to %c ;\n" printEncExp (model, texp) ch
							else if (not isoutermodeenc && isprevmodeenc && not iscurmodeenc) then
								Printf.fprintf oc ");\n Output %a to _ ;\n" printEncExp (model, texp)
							else 
								Printf.fprintf oc "enclave(%d, \n Output %a to _;\n" curencid printEncExp (model, texp)
							in
						let _ = printEnclaveend oc (isoutermodeenc, isprevmodeenc, iscurmodeenc, curencid, tail, model, k'') in
						loop isoutermodeenc iscurmodeenc curencid tail
			| (TIf(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, encexp, ttrue, tfalse, gamma', k'), k'')::tail -> 
						let iscurmodeenc = if (ModeSAT.find (get_mode_var mu) model)=1 then true else false in
						let curencid	 = if iscurmodeenc then
										get_enclave_id model mu 
								   else
										-1 
								   in
						let isprevencsame = if (curencid = prevencid) then true else false in
						let _ = if (isoutermodeenc)||(isprevmodeenc && iscurmodeenc && isprevencsame) || (not iscurmodeenc) || 
										(not isoutermodeenc && isprevmodeenc && not iscurmodeenc)	 then
							Printf.fprintf oc "if %a then \n %a \n else \n %a \n fi;\n" printeexp (model, encexp) printEncProgram  (model, iscurmodeenc, ttrue) printEncProgram (model, iscurmodeenc, tfalse) 
							else if (not isoutermodeenc && isprevmodeenc && not iscurmodeenc) then
							Printf.fprintf oc ");\n if %a then \n %a \n else \n %a \n fi; \n" printeexp (model, encexp) printEncProgram  (model, iscurmodeenc, ttrue) printEncProgram (model, iscurmodeenc, tfalse) 
							else 
							Printf.fprintf oc "enclave(%d, \n if %a then \n %a \n else \n %a \n fi;\n" curencid printeexp (model, encexp) printEncProgram  (model, iscurmodeenc, ttrue) printEncProgram (model, iscurmodeenc, tfalse) 
						in
						let _ = printEnclaveend oc (isoutermodeenc, isprevmodeenc, iscurmodeenc, curencid, tail, model, k'') in
						loop isoutermodeenc iscurmodeenc curencid tail
			| (TWhile(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, encexp, tbody, gamma', k'), k'')::tail ->
						let iscurmodeenc = if (ModeSAT.find (get_mode_var mu) model)=1 then true else false in
						let curencid	 = if iscurmodeenc then
										get_enclave_id model mu 
								   else
										-1 
								   in
						let isprevencsame = if (curencid = prevencid) then true else false in
						let _ = if (isoutermodeenc)||(isprevmodeenc && iscurmodeenc && isprevencsame ) || (not iscurmodeenc) ||
										(not isoutermodeenc && isprevmodeenc && not iscurmodeenc)	 then
								Printf.fprintf oc "while %a do \n %a \n end;\n" printeexp (model, encexp) printEncProgram  (model, iscurmodeenc, tbody) 
							else if (not isoutermodeenc && isprevmodeenc && not iscurmodeenc) then
								Printf.fprintf oc ");\n while %a do \n %a \n end;\n" printeexp (model, encexp) printEncProgram  (model, iscurmodeenc, tbody) 
							else
								Printf.fprintf oc "enclave(%d, \n while %a do \n %a \n end;\n" curencid printeexp (model, encexp) printEncProgram  (model, iscurmodeenc, tbody) 
							in
							let _ = printEnclaveend oc (isoutermodeenc, isprevmodeenc, iscurmodeenc, curencid, tail, model, k'') in
							loop isoutermodeenc iscurmodeenc curencid tail
			| (TCall(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, texp,  gamma', k'), k'')::tail->
						let iscurmodeenc = if (ModeSAT.find (get_mode_var mu) model)=1 then true else false in
						let curencid	 = if iscurmodeenc then
										get_enclave_id model mu 
								   else
										-1 
								   in
						let isprevencsame = if (curencid = prevencid) then true else false in
						let _ = if (isoutermodeenc)||(isprevmodeenc && iscurmodeenc && isprevencsame) || (not iscurmodeenc) ||
										(not isoutermodeenc && isprevmodeenc && not iscurmodeenc)	 then
								Printf.fprintf oc "call(%a);\n" printEncExp (model, texp)
							else if (not isoutermodeenc && isprevmodeenc && not iscurmodeenc) then
								Printf.fprintf oc ");\n call(%a);\n" printEncExp (model, texp)
							else 
								Printf.fprintf oc "enclave(%d, \n call(%a);\n" curencid printEncExp (model, texp)
							in
						let _ = printEnclaveend oc (isoutermodeenc, isprevmodeenc, iscurmodeenc, curencid, tail, model, k'') in
						loop isoutermodeenc iscurmodeenc curencid tail
			| _ -> raise (TranslationError "Expecting non-Sequence judgment") 
			end in
		let curencid	 = if isoutermodeenc then
						get_enclave_id model mu 
				   else
						-1 
				   in
		let isprevmodeenc  = if isoutermodeenc then true else false in
		loop isoutermodeenc isprevmodeenc  curencid tstmtlist  	
| TSkip(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, gamma', k')->
		let iscurmodeenc = if (ModeSAT.find (get_mode_var mu) model)=1 then true else false in
		if (isoutermodeenc)|| (not iscurmodeenc) then
				Printf.fprintf oc "skip\n" 
		else (* if (not isoutermodeenc)&&(not isprevmodeenc)&&(iscurmodeenc) then *)
				let id = get_enclave_id model mu in
				Printf.fprintf oc "enclave(%d, \n skip)\n " id
| TSetcnd(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, cnd, gamma', k')->
			let iscurmodeenc = if (ModeSAT.find (get_mode_var mu) model)=1 then true else false in
			if (isoutermodeenc)|| (not iscurmodeenc) then
				Printf.fprintf oc "set(%s)\n" cnd 
			else (* if (not isoutermodeenc)&&(not isprevmodeenc)&&(iscurmodeenc) then *)
				let id = get_enclave_id model mu in
				Printf.fprintf oc "enclave(%d, \n set(%s))\n" id cnd 

| TAssign (pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, x, texp, gamma', k')->
			let iscurmodeenc = if (ModeSAT.find (get_mode_var mu) model)=1 then true else false in
			if (isoutermodeenc)|| (not iscurmodeenc) then
				Printf.fprintf oc "%s:= %a\n" x  printEncExp (model, texp) 
			else (* if (not isoutermodeenc)&&(not isprevmodeenc)&&(iscurmodeenc) then *)
				let id = get_enclave_id model mu in
				Printf.fprintf oc "enclave(%d, \n %s:= %a)\n" id x printEncExp (model, texp)  
| TDeclassify(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, x, texp, gamma', k')->
			let iscurmodeenc = if (ModeSAT.find (get_mode_var mu) model)=1 then true else false in
			if (isoutermodeenc)|| (not iscurmodeenc) then
				Printf.fprintf oc "%s:= declassify(%a)\n" x  printEncExp (model, texp) 
			else (* if (not isoutermodeenc)&&(not isprevmodeenc)&&(iscurmodeenc) then *)
				let id = get_enclave_id model mu in
				Printf.fprintf oc "enclave(%d, \n %s:= declassify(%a))\n" id x printEncExp (model, texp)  
| TUpdate(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, texp1, texp2, gamma', k')->
			let iscurmodeenc = if (ModeSAT.find (get_mode_var mu) model)=1 then true else false in
			if (isoutermodeenc)|| (not iscurmodeenc) then
				Printf.fprintf oc "%a <- %a \n" printEncExp (model, texp1)  printEncExp (model, texp2) 
			else (* if (not isoutermodeenc)&&(not isprevmodeenc)&&(iscurmodeenc) then *)
				let id = get_enclave_id model mu in
				Printf.fprintf oc "enclave(%d, \n %a <- %a)\n" id  printEncExp (model, texp1) printEncExp (model, texp2)  
| TOut(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, ch, texp, gamma', k')->
			let iscurmodeenc = if (ModeSAT.find (get_mode_var mu) model)=1 then true else false in
			if (isoutermodeenc)|| (not iscurmodeenc) then
				Printf.fprintf oc "Output %a to _ \n" printEncExp (model, texp)
			else (* if (not isoutermodeenc)&&(not isprevmodeenc)&&(iscurmodeenc) then *)
				let id = get_enclave_id model mu in
				Printf.fprintf oc "enclave(%d, \n Output %a to _)\n" id printEncExp (model, texp)
| TIf(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, encexp, ttrue, tfalse, gamma', k')-> 
			let iscurmodeenc = if (ModeSAT.find (get_mode_var mu) model)=1 then true else false in
			if (isoutermodeenc)|| (not iscurmodeenc) then
				Printf.fprintf oc "if %a then \n %a \n else \n %a" printeexp (model, encexp) printEncProgram  (model, iscurmodeenc, ttrue) printEncProgram (model, iscurmodeenc, tfalse) 
			else (* if (not isoutermodeenc)&&(not isprevmodeenc)&&(iscurmodeenc) then *)
				let id = get_enclave_id model mu in
				Printf.fprintf oc "enclave(%d, \n if %a then \n %a \n else \n %a)\n" id  printeexp (model, encexp) printEncProgram  (model, iscurmodeenc, ttrue) printEncProgram (model, iscurmodeenc, tfalse) 
| TWhile(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, encexp, tbody, gamma', k')->
			let iscurmodeenc = if (ModeSAT.find (get_mode_var mu) model)=1 then true else false in
			if (isoutermodeenc)|| (not iscurmodeenc) then
				Printf.fprintf oc "while %a do \n %a \n end \n" printeexp (model, encexp) printEncProgram  (model, iscurmodeenc, tbody) 
			else (* if (not isoutermodeenc)&&(not isprevmodeenc)&&(iscurmodeenc) then *)
				let id = get_enclave_id model mu in
				Printf.fprintf oc "enclave(%d, \n while %a do \n %a \n end) \n" id printeexp (model, encexp) printEncProgram  (model, iscurmodeenc, tbody) 
| TCall(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, texp,  gamma', k')->
			let iscurmodeenc = if (ModeSAT.find (get_mode_var mu) model)=1 then true else false in
			if (isoutermodeenc)|| (not iscurmodeenc) then
				Printf.fprintf oc "call(%a)\n" printEncExp (model, texp)
			else (* if (not isoutermodeenc)&&(not isprevmodeenc)&&(iscurmodeenc) then *)
				let id = get_enclave_id model mu in
				Printf.fprintf oc "enclave(%d, \n call(%a))\n" id printEncExp (model, texp)

and printEncExp oc (model, texp) = match texp with
|TExp(srcgamma,e,srctype, mu,gamma',delta,ence,enctype) -> printeexp oc (model, ence)
|TLamExp(srcgamma,e,srctype, mu,gamma,delta',tstmt,enctype) -> let mu' = get_translated_stmt_mode tstmt in
						begin match mu' with
						|ModeVar(x, _) ->let iscurmodeenc = if (ModeSAT.find x model) = 1 then true else false in
								let id = get_enclave_id model mu in
								Printf.fprintf oc "(lambda^(%d, %d)(_,_,_,_,_).%a)" (ModeSAT.find x model) id printEncProgram (model, iscurmodeenc, tstmt)
						| _ ->raise (TranslationError "Not a mode variable??!")
						end

and printeexp oc  (model, e) = match e with
  | EVar v -> Printf.fprintf oc "%s" v
  | ELam(ModeVar(x, _), pre, kpre, p, u, post, kpost, q, s) -> raise (TranslationError "Can't print function")
  | EPlus (l,r) -> Printf.fprintf oc "%a + %a" printeexp (model, l) printeexp (model, r)
  | EModulo (l,r) -> Printf.fprintf oc "%a %% %a" printeexp (model, l) printeexp (model, r)
  | EConstant n -> Printf.fprintf oc "%d" n
  | EArray(ModeVar(x,_), li) -> Printf.fprintf oc "(%a)" printArrayLoc li
  | ELiteral s -> Printf.fprintf oc "%s" s
  | ETuple(f,s) -> Printf.fprintf oc "(%a, %a)" printeexp (model, f)  printeexp (model, s)
  | ETrue ->  Printf.fprintf oc "true"
  | EFalse -> Printf.fprintf oc "false"
  | EEq (l,r) -> Printf.fprintf oc "%a == %a" printeexp (model, l) printeexp (model, r)
  | ENeq (l,r) -> Printf.fprintf oc "%a != %a" printeexp (model, l) printeexp (model, r)
  | ELt (l,r) -> Printf.fprintf oc "%a < %a" printeexp (model, l) printeexp (model, r)
  | EFst e   -> Printf.fprintf oc "fst %a" printeexp (model, e)
  | ESnd e   -> Printf.fprintf oc "snd %a" printeexp (model, e)
  | ELoc (_, l) ->Printf.fprintf oc "l%d" l
  | EIndex(_,e', eidx) ->Printf.fprintf oc "%a[%a]" printeexp (model, e') printeexp (model, eidx)
  | EDeref e -> Printf.fprintf oc "*%a" printeexp (model, e)
  | EIsunset x -> Printf.fprintf oc "isunset(%s)" x

let rec printEncBaseType oc (model, value) = match value with
  |EBtRef (mu, lt')  -> let iscurmodeenc = if (ModeSAT.find (get_mode_var mu) model) = 1 then true else false in
			    let id = get_enclave_id model mu in
			   Printf.fprintf oc "%a^(%d, %d) ref" printEncType (model, lt')  (ModeSAT.find (get_mode_var mu) model) id 
  | EBtInt  			-> Printf.fprintf oc "int" 
  | EBtBool			->Printf.fprintf oc "bool" 
  | EBtString 			->Printf.fprintf oc "string" 
  | EBtPair (b1, b2)		->Printf.fprintf oc "(%a, %a)" printEncBaseType (model, b1) printEncBaseType (model, b2) 
  | EBtArray (mu, i, lt) 	->
				  let iscurmodeenc = if (ModeSAT.find (get_mode_var mu) model) = 1 then true else false in
			          let id = get_enclave_id model mu in
				  Printf.fprintf oc "(%a^(%d, %d) [%d])" printEncType (model, lt) (ModeSAT.find (get_mode_var mu) model) id  i 
  | EBtCond mu			->
				  let iscurmodeenc = if (ModeSAT.find (get_mode_var mu) model) = 1 then true else false in
			          let id = get_enclave_id model mu in
				  Printf.fprintf oc "cond^(%d, %d)" (ModeSAT.find (get_mode_var mu) model) id 
  | EBtFunc (mu, gpre1, kpre, p, cset, gpost, kpost) -> ()

and printEncType oc (model, value) = match value with
 |(EBtRef (mu, lt') , p) -> let iscurmodeenc = if (ModeSAT.find (get_mode_var mu) model) = 1 then true else false in
			    let id = get_enclave_id model mu in
				Printf.fprintf oc "%a^(%d, %d) ref_%a" printEncType (model, lt')  (ModeSAT.find (get_mode_var mu) model) id printPolicy p
  | EBtInt, p  			-> Printf.fprintf oc "int_%a" printPolicy p
  | EBtBool, p			->Printf.fprintf oc "bool_%a" printPolicy p
  | EBtString, p 		->Printf.fprintf oc "string_%a" printPolicy p
  | EBtPair (b1, b2), p		->Printf.fprintf oc "(%a, %a)_%a" printEncBaseType (model, b1) printEncBaseType (model, b2) printPolicy p
  | EBtArray (mu, i, lt), p 	->
				  let iscurmodeenc = if (ModeSAT.find (get_mode_var mu) model) = 1 then true else false in
			          let id = get_enclave_id model mu in
				  Printf.fprintf oc "(%a^(%d, %d) [%d])_%a" printEncType (model, lt) (ModeSAT.find (get_mode_var mu) model) id  i printPolicy p
  | EBtCond mu, p		->
				  let iscurmodeenc = if (ModeSAT.find (get_mode_var mu) model) = 1 then true else false in
			          let id = get_enclave_id model mu in
				  Printf.fprintf oc "cond^(%d, %d)_%a" (ModeSAT.find (get_mode_var mu) model) id printPolicy p
  | EBtFunc (mu, gpre1, kpre, p, cset, gpost, kpost), q -> ()

let rec printEncLocTypes oc (model, genc) = VarLocMap.iter (fun key value -> match key with
						| Reg x -> Printf.fprintf oc "%s: %a;\n" x printEncType (model, value)
						| Mem l -> Printf.fprintf oc "l%d: %a;\n" l printEncType (model, value)
						) genc
