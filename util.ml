open Unix
open Printf
open Ast
open Helper

exception ModeError of string
exception EidSelectionError of string

(* Execute solver and read back output in string *)
let read_process command =
  let buffer_size = 2048 in
  let buffer = Buffer.create buffer_size in
  let string = Bytes.create buffer_size in
  let in_channel = Unix.open_process_in command in
  let chars_read = ref 1 in
  while !chars_read <> 0 do
    chars_read := input in_channel string 0 buffer_size;
    Buffer.add_substring buffer string 0 !chars_read
  done;
  ignore (Unix.close_process_in in_channel);
  Buffer.contents buffer

let ismodevar xstr ms =
 let elems = ModeSet.elements ms in
 let rec check_rho_exists elemlist = begin match elemlist with
 |[] -> false
 |xs::tail -> begin match xs with
		| ModeVar (x, _) -> if x = xstr then true else	
					check_rho_exists tail
		| _ -> raise (ModeError "Can't have this mode in a mode variable")
	      end
 end
 in check_rho_exists elems 

 let iskillvar xstr klist =
 	List.exists (fun elm -> xstr = elm ) klist

let parse_model inp model ms klist : modesat =
 let xlist = Str.split (Str.regexp " ") inp in
 let rec loop xs model isbreak  = 
  match xs with
  | [] -> model
  | x::tail -> 
		(* Toysat has a different format. Gets \nv and \n*)
	    if isbreak then model 
	    else
		let xsign, pos, len' =
			let len = String.length x in
			let iszero = (Char.compare x.[0] '-') in
					if iszero = 0 then (0,1, len-1) else (1,0, len)
		 in
		let xstr' = String.sub x pos len' in
		let islastcharnv = (Char.compare xstr'.[len'-1] 'v') in
		let islastcharn = (Char.compare xstr'.[len'-1] '\n') in
		let xstr = if islastcharnv = 0 then
				(* Remove last 2 chars *)
				String.sub xstr' 0  (len' - 2)
			    else  
				if islastcharn=0 then
					String.sub xstr' 0  (len' - 1)
				else
					xstr'
		in
		(* Check if xstr is a mode variable or bij *)
		let model' = if (iskillvar xstr klist) then
				ModeSAT.add (Kvar xstr) xsign model
			     else if not (ismodevar xstr ms) then
				ModeSAT.add (Eid xstr) xsign model
			     else
				ModeSAT.add (Mode (ModeVar (xstr, "dummy"))) xsign model
		in
		let isbreak = if islastcharn = 0 then true else false
		in loop tail model' isbreak
 in loop xlist model false

let extractsatmodel  inp eidmap klist : modesat =
  let pos = Str.search_forward (Str.regexp "OPTIMUM FOUND") inp 0 in
  let _ = Printf.printf "Position: %d\n" pos in
  let start = Str.search_forward (Str.regexp "v ") inp pos in
  
  let _ = Printf.printf "V Position: %d\n" start in
  let posend = Str.search_forward (Str.regexp "c ") inp start in
  let _ = Printf.printf "C Position: %d\n" posend in

  let extractsat = String.sub inp (start + 2) (posend - start -2) in
  let _ = Printf.printf "%s\n" extractsat  in
  parse_model extractsat ModeSAT.empty eidmap klist




let fill_enclave_ids eidset = 
  let i = 0 in
  let rec fill_numeric_ids eidset i =
	let n = number_of_enclaves in
	if VarSet.cardinal eidset = n then
		eidset
	else
		let eidset' = VarSet.add (string_of_int i) eidset in
		let i' = (i + 1) in
		fill_numeric_ids eidset' i'
  in fill_numeric_ids eidset i

let get_mode = function
| ModeVar(x, _) -> x
| _ -> raise (ModeError "Unknown mode format.")

 (* Assign id to each element of ms *) 
let assign_rho_ids ms model eidset eidrevmap = 
 let rec unify_rho_ids ms updatedmodeset  eidconstraints = 
    if not (ModeSet.is_empty ms) then begin
	let rho1 = ModeSet.choose ms in
	let ms' = ModeSet.remove rho1 ms in
	let rho1eidconstraints = if EnclaveidConstraints.mem rho1 eidconstraints then
						EnclaveidConstraints.find rho1 eidconstraints
				 else
						VarSet.empty
	in	
        if not (ModeSet.is_empty ms') then 
 	   let rho2 = ModeSet.choose ms' in
	   let ms'' = ModeSet.remove rho2 ms' in
	   (* Get bij corresponding to rho1 and rho2 *)
	   (* Note: Because of fill_enclave_ids, binding should exist *)
	   let bijvar = EnclaveidRevMap.find (rho1, rho2) eidrevmap in
	
	   (* See if bijvar is set to 1/0 in model *)
	   let bij = ModeSAT.find (Eid bijvar) model in
	
	   let rho2eidconstraints = if EnclaveidConstraints.mem rho1 eidconstraints then
						EnclaveidConstraints.find rho1 eidconstraints
				 else
						VarSet.empty
	   in		
	   (* if bij = 0, assign same identifier *)
	   let (eid1, eid2) = if (bij = 0) then 
				let rec select_satisfying_id eidset =
					if (VarSet.is_empty eidset) then raise (EidSelectionError "Could not select satisfying enclave id")
					else
					let eid = VarSet.choose eidset in
					(* See if eid is in prohibhited list *)
					if (VarSet.mem eid rho1eidconstraints) || (VarSet.mem eid rho2eidconstraints) then
						(* Remove eid and call recursively - for faster convergence *)
						let eidset' = VarSet.remove eid eidset in
						select_satisfying_id eidset'
					else
						(eid, eid)
				in select_satisfying_id eidset	
			      else 
				(* check if rho1 satisfies *)
				let rec select_satisfying_id eidset =
					if (VarSet.is_empty eidset) then raise (EidSelectionError "Could not select satisfying enclave id")
					else
					let eid = VarSet.choose eidset in
					(* See if eid is in prohibhited list *)
					if (VarSet.mem eid rho1eidconstraints) then
						(* Remove eid and call recursively - for faster convergence *)
						let eidset' = VarSet.remove eid eidset in
						select_satisfying_id eidset'
					else
						eid
				in 
				let eid1 = select_satisfying_id eidset in
				let rec select_diff_id eid1 eidset=
					if (VarSet.is_empty eidset) then raise (EidSelectionError "Could not select satisfying enclave id")
					else
					let eid2 = VarSet.choose eidset in
					(* See if eid2 is in prohibhited list *)
					if (VarSet.mem eid2 rho2eidconstraints) then
						(* Remove eid and call recursively - for faster convergence *)
						let eidset' = VarSet.remove eid2 eidset in
						select_diff_id eid1 eidset'
					else if (eid1 = eid2) then 
						(* Remove eid and call recursively - for faster convergence *)
						let eidset' = VarSet.remove eid2 eidset in
						select_diff_id eid1 eidset'
					else eid2
				in
				let eid2 = select_diff_id  eid1  eidset in
				(eid1, eid2)
	  in
	
	  let rho1var = get_mode rho1 in
	  let rho2var = get_mode rho2 in
          let updatedmodeset' = ModeSet.add  (ModeVar (rho1var, eid1)) updatedmodeset in 	 
          let updatedmodeset'' = ModeSet.add  (ModeVar (rho2var, eid2)) updatedmodeset' in 	 

	  (* Also check if rho1/rho2 has constraints with other modes. If so, unify them *)
	  (* get a filter where rho1 is present *)
	  let rho1eidrevmap = EnclaveidRevMap.filter (fun key a -> if ((fst key) = rho1) || ((snd key) = rho1) then
									true
								   else false) eidrevmap
	  in 
	  (* find all bij corresponding to this map *)
	  let rho1revmaplist = EnclaveidRevMap.bindings rho1eidrevmap in
	  
	 let rec assign_id_to_rho1_list rho1list ms updatedmodeset eidconstraints = begin match rho1list with
		|[] -> (updatedmodeset, ms, eidconstraints)
		|((rho', rho''), bikvar)::tail -> let rho = if rho' = rho1 then rho'' else rho' in
					       let rhovar = get_mode rho in
	   					(* See if bijvar is set to 1/0 in model *)
	   					let bik = ModeSAT.find (Eid bijvar) model in
					       
					       let (updatedmodeset', ms', eidconstraints') =  
							if bik = 0 then (ModeSet.add (ModeVar (rhovar, eid1)) updatedmodeset,  ModeSet.remove rho' ms, eidconstraints)
					       		else
								let prohibhitedids = if (EnclaveidConstraints.mem rho eidconstraints) then
											     	EnclaveidConstraints.find rho eidconstraints
								     		     else
												VarSet.empty
								in (updatedmodeset, ms,  EnclaveidConstraints.add rho (VarSet.add eid1 prohibhitedids) eidconstraints)
						in assign_id_to_rho1_list tail ms' updatedmodeset' eidconstraints'
		end
	in 
	let (updatedmodeset1, ms1, eidconstraints1) = assign_id_to_rho1_list rho1revmaplist ms'' updatedmodeset''  eidconstraints in
	  (* get a filter where rho2 is present *)
	let rho2eidrevmap = EnclaveidRevMap.filter (fun key a -> if ((fst key) = rho2) || ((snd key) = rho2) then
									true
								   else false) eidrevmap
	in 
	  (* find all bij corresponding to this map *)
        let rho2revmaplist = EnclaveidRevMap.bindings rho2eidrevmap in
	let rec assign_id_to_rho2_list rho2list ms updatedmodeset eidconstraints = begin match rho2list with
		|[] -> (updatedmodeset, ms, eidconstraints)
		|((rho', rho''), bjk)::tail -> let rho = if rho' = rho2 then rho'' else rho' in
					       let rhovar = get_mode rho in
	   					(* See if bijvar is set to 1/0 in model *)
	   					let bjk = ModeSAT.find (Eid bijvar) model in
					       let (updatedmodeset', ms', eidconstraints') =  
							if bjk = 0 then (ModeSet.add (ModeVar (rhovar, eid2)) updatedmodeset,  ModeSet.remove rho' ms, eidconstraints)
					       		else
								let prohibhitedids = if (EnclaveidConstraints.mem rho eidconstraints) then
											     	EnclaveidConstraints.find rho eidconstraints
								     		     else
												VarSet.empty
								in (updatedmodeset, ms,  EnclaveidConstraints.add rho (VarSet.add eid2 prohibhitedids) eidconstraints)
						in assign_id_to_rho2_list tail ms' updatedmodeset' eidconstraints'
		end
	 in
	 let (updatedmodeset2, ms2, eidconstraints2) = assign_id_to_rho2_list rho2revmaplist ms1 updatedmodeset1  eidconstraints1 in
	 		 unify_rho_ids ms2 updatedmodeset2 eidconstraints2
      else
          (* modeset has only element *)
	  let rec select_satisfying_id eidset =
			if (VarSet.is_empty eidset) then raise (EidSelectionError "Could not select satisfying enclave id")
			else
				let eid = VarSet.choose eidset in
				(* See if eid is in prohibhited list *)
				if (VarSet.mem eid rho1eidconstraints) then
					(* Remove eid and call recursively - for faster convergence *)
					let eidset' = VarSet.remove eid eidset in
					select_satisfying_id eidset'
				else
					eid
	  in 
	  let eid1 = select_satisfying_id eidset in
	  let rho1var = get_mode rho1 in
          let updatedmodeset' = ModeSet.add (ModeVar (rho1var, eid1)) updatedmodeset in 	 
	   (updatedmodeset', ms', eidconstraints)
     end
    else
	(updatedmodeset, ms, eidconstraints)	
 in unify_rho_ids ms ModeSet.empty EnclaveidConstraints.empty
