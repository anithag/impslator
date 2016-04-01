open Ast
open Printf
open Pprint
open Helper

exception PrintError
exception TranslationError of string
exception IdNotFound of string

let rec get_resolved_enclave_id model_with_ids rho =
	let elm  = (try ModeSet.choose model_with_ids with Not_found-> raise (IdNotFound "Id not found for enclave")) in
	let (rho', id') = begin match elm with
		   		|ModeVar (rho', id') -> (rho', id')
				|_ -> raise (IdNotFound "Weird Constructor")
			  end in
	 if rho' == rho then id' else
	   get_resolved_enclave_id (ModeSet.remove elm model_with_ids) rho

(* Check if last statement has a kill *)
let rec helperfunc2 listtoprint model = 
 let len = List.length listtoprint in
 if (len = 0) then false
 else
     match (List.nth listtoprint (len-1) ) with 
	|EIf (rho', e, s1, s2, alpha) ->( try 
					if (ModeSAT.find (Kvar alpha) model) = 1 then
						true
				   	else
						false
					with Not_found -> false)
  	|ESkip(rho', rho'', alpha) ->( try  
				     if (ModeSAT.find (Kvar alpha) model) = 1 then
						true
				   	else
						false
					with Not_found -> false)
  	|EAssign (rho',v,e, alpha)  -> ( try 
					if (ModeSAT.find (Kvar alpha) model) = 1 then
						true
				   	else
						false
					with Not_found -> false)
	|EDeclassify(rho',v,e, alpha) -> ( try 
					if (ModeSAT.find (Kvar alpha) model) = 1 then
						true
				   	else
						false
					with Not_found -> false)
  	|EUpdate (rho', e1, e2, alpha) -> ( try 
					if (ModeSAT.find (Kvar alpha) model) = 1 then
						true
				   	else
						false
					with Not_found -> false)
  	|ESeq  (rho', s1, s2, alpha) -> ( try 
					if (ModeSAT.find (Kvar alpha) model) = 1 then
						true
				   	else
						false
					with Not_found -> false)
  	|EESeq  (rho', es, alpha) -> ( try 
					if (ModeSAT.find (Kvar alpha) model) = 1 then
						true
				   	else
						false
					with Not_found -> false)
  	|EWhile  (rho', e, es, alpha) ->( try 
					 if (ModeSAT.find (Kvar alpha) model) = 1 then
						true
				   	else
						false
					with Not_found -> false)
  	|EOutput (rho', ch, e, alpha) ->( try 
					 if (ModeSAT.find (Kvar alpha) model) = 1 then
						true
				   	else
						false
					with Not_found -> false)
  	|ECall  (rho', e, alpha)  ->( try 
					 if (ModeSAT.find (Kvar alpha) model) = 1 then
						true
				   	else
						false
					with Not_found -> false)
	|ESet  (rho', v, alpha) ->( try 
				 if (ModeSAT.find (Kvar alpha) model) = 1 then
					true
				  else
					false
					with Not_found -> false)

let rec translate oc (model_with_ids, model, encstmt, rho) = match encstmt with
 |EESeq (ModeVar(rho, _), estmtlist, alpha) ->let rhoisenclave = ModeSAT.find (Mode (ModeVar(rho, "dummy")))  model in 
			   let rec dispatch listtoprint estmtlist = begin match estmtlist with
				|[] -> let _ = if List.length listtoprint = 0 then () 
					       else if (rhoisenclave=1) then
							(* already part of enclave *)
							Printf.fprintf oc " %a " printeprog (model_with_ids, model, listtoprint) 
						else
							Printf.fprintf oc "enclave (\n %a \n )" printeprog (model_with_ids, model, listtoprint) 
					in ()
				|est::tail -> begin match est with 
   					|EIf (rho', e, s1, s2, alpha)-> let (list', newline) = helperfunc rhoisenclave rho' model_with_ids model listtoprint est oc in
	     							 let _ = if (not (List.length tail = 0)) && newline then Printf.fprintf oc "; \n" else () in  
								 dispatch list' tail
  					|ESkip(rho', rho'', alpha)->let (list', newline) = helperfunc rhoisenclave rho' model_with_ids model listtoprint est oc in
	     							 let _ = if (not (List.length tail = 0)) && newline then Printf.fprintf oc "; \n" else () in  
								 dispatch list' tail
  					|EAssign (rho',v,e, alpha) 
					|EDeclassify(rho',v,e, alpha) ->let (list', newline) = helperfunc rhoisenclave rho' model_with_ids model listtoprint est oc in
	     							 let _ = if (not (List.length tail = 0)) && newline then Printf.fprintf oc "; \n" else () in  
								 dispatch list' tail
  					|EUpdate (rho', e1, e2, alpha)->let (list', newline) = helperfunc rhoisenclave rho' model_with_ids model listtoprint est oc in 
	     							 let _ = if (not (List.length tail = 0)) && newline then Printf.fprintf oc "; \n" else () in  
								 dispatch list' tail
  					|ESeq  (rho', s1, s2, alpha) ->let (list', newline) = helperfunc rhoisenclave rho' model_with_ids model listtoprint est oc in
	     							 let _ = if (not (List.length tail = 0)) && newline then Printf.fprintf oc "; \n" else () in  
								 dispatch list' tail
  					|EESeq  (rho', es, alpha) ->let (list', newline) = helperfunc rhoisenclave rho' model_with_ids model listtoprint est oc in
	     							 let _ = if (not (List.length tail = 0)) && newline then Printf.fprintf oc "; \n" else () in  
								 dispatch list' tail
  					|EWhile  (rho', e, es, alpha) ->let (list', newline) = helperfunc rhoisenclave rho' model_with_ids model listtoprint est oc in
	     							 let _ = if (not (List.length tail = 0)) && newline then Printf.fprintf oc "; \n" else () in  
								 dispatch list' tail
  					|EOutput (rho', ch, e, alpha) ->let (list', newline) = helperfunc rhoisenclave rho' model_with_ids model listtoprint est oc in
	     							 let _ = if (not (List.length tail = 0)) && newline then Printf.fprintf oc "; \n" else () in  
								 dispatch list' tail
  					|ECall  (rho', e, alpha) ->let (list', newline) = helperfunc rhoisenclave rho' model_with_ids model listtoprint est oc in
	     							 let _ = if (not (List.length tail = 0)) && newline then Printf.fprintf oc "; \n" else () in  
								 dispatch list' tail
					|ESet  (rho', v, alpha) ->  let (list', newline)= helperfunc rhoisenclave rho' model_with_ids model listtoprint est oc in
	     							 let _ = if (not (List.length tail = 0)) && newline then Printf.fprintf oc "; \n" else () in  
								 dispatch list' tail
				end
			end
			in dispatch [] estmtlist
|EIf (ModeVar(rho',_), e, s1, s2, alpha)-> 
			let rhoisenclave = ModeSAT.find rho model in
 			 let rho'isenclave = ModeSAT.find (Mode (ModeVar(rho', "dummy")))  model in 
			 (try
			 if (rhoisenclave = 0) && (rho'isenclave=1) && ((ModeSAT.find (Kvar alpha) model)=1) then
			 	Printf.fprintf oc "enclave(%s, %a );\n kill()" (get_resolved_enclave_id model_with_ids rho') printestmt (model_with_ids, model, encstmt)
			 else if ((rhoisenclave=1) && (rho'isenclave=1)) || ((rhoisenclave=0) && (rho'isenclave=0)) then
			 	Printf.fprintf oc " %a " printestmt (model_with_ids, model, encstmt) 
		         else raise (TranslationError "Incorrect mode assignment")
			 with 
			 Not_found -> if (rhoisenclave = 0) && (rho'isenclave=1) then 
			 	Printf.fprintf oc "enclave(%s, %a )" (get_resolved_enclave_id model_with_ids rho') printestmt (model_with_ids, model, encstmt)
			 else if ((rhoisenclave=1) && (rho'isenclave=1)) || ((rhoisenclave=0) && (rho'isenclave=0)) then
			 	Printf.fprintf oc " %a " printestmt (model_with_ids, model, encstmt) 
		         else raise (TranslationError "Incorrect mode assignment")
			 )
|ESkip(ModeVar(rho',_), rho'', alpha)->
			 let rhoisenclave = ModeSAT.find rho model in
 			 let rho'isenclave = ModeSAT.find (Mode (ModeVar(rho', "dummy")))  model in 
			 (try
			 if (rhoisenclave = 0) && (rho'isenclave=1) && ((ModeSAT.find (Kvar alpha) model)=1) then
			 	Printf.fprintf oc "enclave(%s, %a );\n kill()" (get_resolved_enclave_id model_with_ids rho')  printestmt (model_with_ids, model, encstmt)
			 else if ((rhoisenclave=1)&& (rho'isenclave=1)) || ((rhoisenclave=0) && (rho'isenclave=0)) then
			 	Printf.fprintf oc " %a " printestmt (model_with_ids, model, encstmt)
		        else raise (TranslationError "Incorrect mode assignment")
			 with 
			 Not_found ->
			 if (rhoisenclave = 0) && (rho'isenclave=1) then
			 	Printf.fprintf oc "enclave(%s, %a )" (get_resolved_enclave_id model_with_ids rho')  printestmt (model_with_ids, model, encstmt)
			 else if ((rhoisenclave=1)&& (rho'isenclave=1)) || ((rhoisenclave=0) && (rho'isenclave=0)) then
			 	Printf.fprintf oc " %a " printestmt (model_with_ids, model, encstmt)
		        else raise (TranslationError "Incorrect mode assignment")
			)
|EAssign (ModeVar(rho',_),v,e, alpha) 
|EDeclassify(ModeVar(rho',_), v, e, alpha) ->
			 let rhoisenclave = ModeSAT.find rho  model in
 			 let rho'isenclave = ModeSAT.find (Mode (ModeVar(rho', "dummy")))  model in 
			 (try
			 if (rhoisenclave = 0) && (rho'isenclave=1) && ((ModeSAT.find (Kvar alpha) model)=1) then
			 	Printf.fprintf oc "enclave(%s, %a );\n kill()" (get_resolved_enclave_id model_with_ids rho')  printestmt (model_with_ids, model, encstmt)
			 else if ((rhoisenclave=1) && (rho'isenclave=1)) || ((rhoisenclave=0) && (rho'isenclave=0)) then
			 	Printf.fprintf oc " %a " printestmt (model_with_ids, model, encstmt)
		        else raise (TranslationError "Incorrect mode assignment")
			 with 
			 Not_found ->
			 if (rhoisenclave = 0) && (rho'isenclave=1) then
			 	Printf.fprintf oc "enclave(%s, %a )" (get_resolved_enclave_id model_with_ids rho')  printestmt (model_with_ids, model, encstmt)
			 else if ((rhoisenclave=1)&& (rho'isenclave=1)) || ((rhoisenclave=0) && (rho'isenclave=0)) then
			 	Printf.fprintf oc " %a " printestmt (model_with_ids, model, encstmt)
		        else raise (TranslationError "Incorrect mode assignment")
			)

|EUpdate (ModeVar(rho',_), e1, e2, alpha)->
			let rhoisenclave = ModeSAT.find rho  model in
 			 let rho'isenclave = ModeSAT.find (Mode (ModeVar(rho', "dummy")))  model in 
			 (try
			 if (rhoisenclave = 0) && (rho'isenclave=1) && ((ModeSAT.find (Kvar alpha) model)=1) then
			 	Printf.fprintf oc "enclave(%s, %a );\n kill()" (get_resolved_enclave_id model_with_ids rho')  printestmt (model_with_ids, model, encstmt)
			 else if ((rhoisenclave=1) && (rho'isenclave=1)) || ((rhoisenclave=0) && (rho'isenclave=0)) then
			 	Printf.fprintf oc " %a " printestmt (model_with_ids, model, encstmt)
		        else raise (TranslationError "Incorrect mode assignment")
			 with 
			 Not_found -> 
			 if (rhoisenclave = 0) && (rho'isenclave=1) then
			 	Printf.fprintf oc "enclave(%s, %a )" (get_resolved_enclave_id model_with_ids rho')  printestmt (model_with_ids, model, encstmt)
			 else if ((rhoisenclave=1)&& (rho'isenclave=1)) || ((rhoisenclave=0) && (rho'isenclave=0)) then
			 	Printf.fprintf oc " %a " printestmt (model_with_ids, model, encstmt)
		        else raise (TranslationError "Incorrect mode assignment")
			)

|ESeq  (ModeVar(rho',_), s1, s2, alpha) ->
			let rhoisenclave = ModeSAT.find rho model in
 			 let rho'isenclave = ModeSAT.find (Mode (ModeVar(rho', "dummy")))  model in 
			 (try
			 if (rhoisenclave = 0) && (rho'isenclave=1) && ((ModeSAT.find (Kvar alpha) model)=1) then
			 	Printf.fprintf oc "enclave(%s, %a );\n kill()" (get_resolved_enclave_id model_with_ids rho')  printestmt (model_with_ids, model, encstmt)
			 else if ((rhoisenclave=1) && (rho'isenclave=1)) || ((rhoisenclave=0) && (rho'isenclave=0)) then
			 	Printf.fprintf oc " %a " printestmt (model_with_ids, model, encstmt)
		        else raise (TranslationError "Incorrect mode assignment")
			 with 
			 Not_found ->
			 if (rhoisenclave = 0) && (rho'isenclave=1) then
			 	Printf.fprintf oc "enclave(%s, %a )" (get_resolved_enclave_id model_with_ids rho')  printestmt (model_with_ids, model, encstmt)
			 else if ((rhoisenclave=1)&& (rho'isenclave=1)) || ((rhoisenclave=0) && (rho'isenclave=0)) then
			 	Printf.fprintf oc " %a " printestmt (model_with_ids, model, encstmt)
		        else raise (TranslationError "Incorrect mode assignment")
			)

|EESeq  (ModeVar(rho',_), es, alpha) ->
			let rhoisenclave = ModeSAT.find rho model in
 			 let rho'isenclave = ModeSAT.find (Mode (ModeVar(rho', "dummy")))  model in 
			 (try
			 if (rhoisenclave = 0) && (rho'isenclave=1) && ((ModeSAT.find (Kvar alpha) model)=1) then
			 	Printf.fprintf oc "enclave(%s, %a );\n kill()" (get_resolved_enclave_id model_with_ids rho')  printestmt (model_with_ids, model, encstmt)
			 else if ((rhoisenclave=1) && (rho'isenclave=1)) || ((rhoisenclave=0) && (rho'isenclave=0)) then
			 	Printf.fprintf oc " %a " printestmt (model_with_ids, model, encstmt)
		        else raise (TranslationError "Incorrect mode assignment")
			 with 
			 Not_found ->
			 if (rhoisenclave = 0) && (rho'isenclave=1) then
			 	Printf.fprintf oc "enclave(%s, %a )" (get_resolved_enclave_id model_with_ids rho')  printestmt (model_with_ids, model, encstmt)
			 else if ((rhoisenclave=1)&& (rho'isenclave=1)) || ((rhoisenclave=0) && (rho'isenclave=0)) then
			 	Printf.fprintf oc " %a " printestmt (model_with_ids, model, encstmt)
		        else raise (TranslationError "Incorrect mode assignment")
			)

|EWhile  (ModeVar(rho',_), e, es, alpha) ->
			 let rhoisenclave = ModeSAT.find rho model in
 			 let rho'isenclave = ModeSAT.find (Mode (ModeVar(rho', "dummy")))  model in 
			 (try
			 if (rhoisenclave = 0) && (rho'isenclave=1) && ((ModeSAT.find (Kvar alpha) model)=1) then
			 	Printf.fprintf oc "enclave(%s, %a );\n kill()" (get_resolved_enclave_id model_with_ids rho')  printestmt (model_with_ids, model, encstmt)
			 else if ((rhoisenclave=1) && (rho'isenclave=1)) || ((rhoisenclave=0) && (rho'isenclave=0)) then
			 	Printf.fprintf oc " %a " printestmt (model_with_ids, model, encstmt)
		        else raise (TranslationError "Incorrect mode assignment")
			 with 
			 Not_found -> 
			 if (rhoisenclave = 0) && (rho'isenclave=1) then
			 	Printf.fprintf oc "enclave(%s, %a )" (get_resolved_enclave_id model_with_ids rho')  printestmt (model_with_ids, model, encstmt)
			 else if ((rhoisenclave=1)&& (rho'isenclave=1)) || ((rhoisenclave=0) && (rho'isenclave=0)) then
			 	Printf.fprintf oc " %a " printestmt (model_with_ids, model, encstmt)
		        else raise (TranslationError "Incorrect mode assignment")
			)

|EOutput (ModeVar(rho',_), ch, e, alpha) ->
			 let rhoisenclave = ModeSAT.find rho model in
 			 let rho'isenclave = ModeSAT.find (Mode (ModeVar(rho', "dummy")))  model in 
			 (try
			 let v = (ModeSAT.find (Kvar alpha) model) = 1 in
			 if (rhoisenclave = 0) && (rho'isenclave=1) && v then 
			 	Printf.fprintf oc "enclave(%s, %a );\n kill()" (get_resolved_enclave_id model_with_ids rho')  printestmt (model_with_ids, model, encstmt)
			 else if ((rhoisenclave=1) && (rho'isenclave=1)) || ((rhoisenclave=0) && (rho'isenclave=0)) then
			 	Printf.fprintf oc " %a " printestmt (model_with_ids, model, encstmt)
		         else raise (TranslationError "Incorrect mode assignment")
			 with 
			 Not_found ->
			 if (rhoisenclave = 0) && (rho'isenclave=1) then
			 	Printf.fprintf oc "enclave(%s, %a )" (get_resolved_enclave_id model_with_ids rho')  printestmt (model_with_ids, model, encstmt)
			 else if ((rhoisenclave=1)&& (rho'isenclave=1)) || ((rhoisenclave=0) && (rho'isenclave=0)) then
			 	Printf.fprintf oc " %a " printestmt (model_with_ids, model, encstmt)
		        else raise (TranslationError "Incorrect mode assignment")
			)
|ECall  (ModeVar(rho',_), e, alpha) ->
			let rhoisenclave = ModeSAT.find rho model in
 			 let rho'isenclave = ModeSAT.find (Mode (ModeVar(rho', "dummy")))  model in 
			 (try
			 if (rhoisenclave = 0) && (rho'isenclave=1) && ((ModeSAT.find (Kvar alpha) model)=1) then
			 	Printf.fprintf oc "enclave(%s, %a );\n kill()" (get_resolved_enclave_id model_with_ids rho')   printestmt (model_with_ids, model, encstmt)
			 else if ((rhoisenclave=1) && (rho'isenclave=1)) || ((rhoisenclave=0) && (rho'isenclave=0)) then
			 	Printf.fprintf oc " %a " printestmt (model_with_ids, model, encstmt)
		        else raise (TranslationError "Incorrect mode assignment")
			 with 
			 Not_found ->
			 if (rhoisenclave = 0) && (rho'isenclave=1) then
			 	Printf.fprintf oc "enclave(%s, %a )" (get_resolved_enclave_id model_with_ids rho')  printestmt (model_with_ids, model, encstmt)
			 else if ((rhoisenclave=1)&& (rho'isenclave=1)) || ((rhoisenclave=0) && (rho'isenclave=0)) then
			 	Printf.fprintf oc " %a " printestmt (model_with_ids, model, encstmt)
		        else raise (TranslationError "Incorrect mode assignment")
			)
|ESet  (ModeVar(rho',_), v, alpha) -> 
			 let rhoisenclave = ModeSAT.find rho model in
 			 let rho'isenclave = ModeSAT.find (Mode (ModeVar(rho', "dummy")))  model in 
			 (try
			 if (rhoisenclave = 0) && (rho'isenclave=1) && ((ModeSAT.find (Kvar alpha) model)=1) then
			 	Printf.fprintf oc "enclave(%s, %a );\n kill()" (get_resolved_enclave_id model_with_ids rho')  printestmt (model_with_ids, model, encstmt)
			 else if ((rhoisenclave=1) && (rho'isenclave=1)) || ((rhoisenclave=0) && (rho'isenclave=0)) then
			 	Printf.fprintf oc " %a " printestmt (model_with_ids, model, encstmt)
		        else raise (TranslationError "Incorrect mode assignment")
			 with 
			 Not_found -> 
			 if (rhoisenclave = 0) && (rho'isenclave=1) then
			 	Printf.fprintf oc "enclave(%s, %a )" (get_resolved_enclave_id model_with_ids rho')  printestmt (model_with_ids, model, encstmt)
			 else if ((rhoisenclave=1)&& (rho'isenclave=1)) || ((rhoisenclave=0) && (rho'isenclave=0)) then
			 	Printf.fprintf oc " %a " printestmt (model_with_ids, model, encstmt)
		        else raise (TranslationError "Incorrect mode assignment")
			)

 | _ -> raise (TranslationError "Translated program should be a list of statements")


and helperfunc rhoisenclave rho' model_with_ids model listtoprint est oc =
		let (rho', rho'var) = begin match rho' with
			   		|ModeVar(rho'var, _ ) -> (ModeVar(rho'var, "dummy"), rho'var)
			   		| _ -> raise (TranslationError "Improper mode assignment")
			   		end in
 		let rho'isenclave = ModeSAT.find (Mode rho')  model in 
		let  (listtoprint', newline) = if (rhoisenclave = 0) && (rho'isenclave=1) then 
					(listtoprint @ [est], false)
		     		    else if (rhoisenclave=1) && (rho'isenclave=1) then
					(listtoprint @ [est], false)
		     		    else if (rhoisenclave=0) && (rho'isenclave=0) then
					let _ = if List.length listtoprint = 0 then () else
						(* Print the list within enclave and then print the normal mode statement *) 
						Printf.fprintf oc "enclave (%s, \n %a \n )" (get_resolved_enclave_id model_with_ids rho'var)  printeprog (model_with_ids, model, listtoprint) in
					let islaststmtkill = helperfunc2 listtoprint model in
					let _ = if islaststmtkill then
						 Printf.fprintf oc "kill();\n"
						else  ()
					in
					let _ = Printf.fprintf oc " %a " printestmt (model_with_ids, model, est) in
						([], true)	
		     		   else raise (TranslationError "Incorrect mode assignment")
		in (listtoprint', newline)


and  printeprog oc (model_with_ids, model, listtoprint) = match listtoprint with
 |[] -> ()
 |xs::tail -> let _ = printestmt oc (model_with_ids, model, xs ) in
	     let _ = if not ( (List.length tail) = 0) then Printf.fprintf oc "; \n" else ()  
 	     in printeprog oc (model_with_ids, model, tail)

 and printestmt oc (model_with_ids, model, encstmt) = match encstmt with 
	|EIf (rho', e, s1, s2, alpha)-> Printf.fprintf oc "if %a then \n %a \n else %a " printeexp (model_with_ids, model, e) translate (model_with_ids, model, s1, (Mode (ModeVar(getrhovar rho', "dummy"))))  translate (model_with_ids, model, s2, (Mode (ModeVar(getrhovar rho', "dummy"))));
  	|ESkip(rho', rho'', alpha)-> Printf.fprintf oc "skip"
  	|EAssign (rho',v,e, alpha)-> Printf.fprintf oc "%s := %a " v  printeexp (model_with_ids, model, e)
  	|EDeclassify(rho',v,e, alpha)-> Printf.fprintf oc "%s := declassify(%a) " v  printeexp (model_with_ids, model, e)
  	|EUpdate (rho', e1, e2, alpha)-> Printf.fprintf oc "%a <- %a " printeexp (model_with_ids, model, e1)  printeexp (model_with_ids, model, e2)
  	|ESeq  (rho', s1, s2, alpha) -> Printf.fprintf oc "%a ; %a " translate (model_with_ids, model, s1, (Mode (ModeVar(getrhovar rho', "dummy"))))  translate (model_with_ids, model, s2, (Mode (ModeVar(getrhovar rho', "dummy"))))  
  	|EESeq  (rho', es, alpha) -> raise (TranslationError "Improper statement to print")
  	|EWhile  (rho', e, es, alpha) ->Printf.fprintf oc "while ( %a ) %a end " printeexp (model_with_ids, model, e) translate (model_with_ids, model, es, (Mode (ModeVar(getrhovar rho', "dummy"))))
  	|EOutput (rho', ch, e, alpha)->Printf.fprintf oc "output %a to %c " printeexp (model_with_ids, model, e) ch
  	|ECall  (rho', e, alpha) ->Printf.fprintf oc "call(%a) " printeexp (model_with_ids, model, e)
  	|ESet  (rho', v, alpha) ->Printf.fprintf oc "set(%s) " v

and printeexp oc  (model_with_ids, model, e) = match e with
  | EVar(rho, v) -> Printf.fprintf oc "%s" v
  | ELam(rho, ModeVar(rho', _), pre, p, u, q, post, s) -> Printf.fprintf oc "(lambda^%d(_,_,_,_,_).%a)" (ModeSAT.find (Mode (ModeVar(rho', "dummy"))) model) translate (model_with_ids, model, s, (Mode (ModeVar(rho', "dummy"))))  
  | EPlus (rho, l,r) -> Printf.fprintf oc "%a + %a" printeexp (model_with_ids, model, l) printeexp (model_with_ids, model, r)
  | EModulo (rho, l,r) -> Printf.fprintf oc "%a %% %a" printeexp (model_with_ids, model, l) printeexp (model_with_ids, model, r)
  | EConstant(rho,n) -> Printf.fprintf oc "%d" n
  | ETrue rho ->  Printf.fprintf oc "true"
  | EFalse rho  -> Printf.fprintf oc "false"
  | EEq (rho, l,r) -> Printf.fprintf oc "%a == %a" printeexp (model_with_ids, model, l) printeexp (model_with_ids, model, r)
  | ENeq (rho, l,r) -> Printf.fprintf oc "%a != %a" printeexp (model_with_ids, model, l) printeexp (model_with_ids, model, r)
  | ELoc(rho, rho', l) ->Printf.fprintf oc "l%d" l
  | EDeref(rho,e) -> Printf.fprintf oc "*%a" printeexp (model_with_ids, model, e)
  | EIsunset(rho,x) -> Printf.fprintf oc "isunset(%s)" x
