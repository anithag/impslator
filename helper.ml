open Ast
open Proplogic

exception HelperError of string


let number_of_enclaves = 2


let labnotlow = function
 | Low -> false
 | _ -> true

let is_array_type = function
 |BtArray (s,li), _ -> true
 | _ -> false

let get_mode = function
| EBtRef(mu', lt), p -> mu'
| EBtArray(mu',_,_), p -> mu'
| EBtFunc(mu', _,_,p,u,_,_), q -> mu'
| _, q ->raise (HelperError "Type has no mode") 

let get_mode_var = function
|ModeVar(mu1, l) -> mu1
| _   -> raise (HelperError "Expected Mode variable")

let get_mode_eidlist = function
|ModeVar(mu1, l) -> l
| _   -> raise (HelperError "Expected Mode variable")

let get_prekillset(t:enclabeltype) =
   match t with
   |EBtFunc(m,gencpre,prekill,p,u, gencpost,postkill), q -> prekill
   |_ -> raise (HelperError "")

let get_postkillset(t:enclabeltype) =
   match t with
   |EBtFunc(m,gencpre,prekill,p,u, gencpost,postkill), q -> postkill
   |_ -> raise (HelperError "")

let get_enc_precontext (t:enclabeltype) =
   match t with
   |EBtFunc(m,gencpre,_,p,u, gencpost,_), q -> gencpre
   |_ -> raise (HelperError "")


let get_enc_postcontext (t:enclabeltype) =
   match t with
   |EBtFunc(m,gencpre,_,p,u, gencpost,_), q -> gencpost
   |_ -> raise (HelperError "")

let get_src_precontext (t:labeltype) =
   match t with
   |BtFunc(gpre,p,u, gpost), q -> gpre
   |_ -> raise (HelperError "")


let get_src_postcontext (t:labeltype) =
   match t with
   |BtFunc(gpre,p,u, gpost), q -> gpost
   |_ -> raise (HelperError "")

let invert_encfunctype = function
  |EBtFunc(m, gencpre, kpre, p, u, gencpost, kpost), q -> (m, gencpre, kpre, p, u, gencpost, kpost)
  | _,q -> raise (HelperError "Expecting function type")

(* Check if base types are same. Ignore policy for comparison 
*)
let rec check_src_base_type b1 b2 = match (b1, b2) with 
  | BtRef lt1, BtRef lt2 -> check_src_base_type (fst lt1) (fst lt2)
  | BtFunc (gpre1, p1, u1, gpost1), BtFunc (gpre2, p2, u2, gpost2) -> 
		      let ispreequal = VarLocMap.equal (fun bp1 bp2 -> 
			begin match (bp1, bp2)  with
			|((b1, p1), (b2, p2)) -> 
				if (p1=p2) && (check_src_base_type b1 b2) then true
				else false
			| _ -> false  
			end) gpre1 gpre2 in
		      let ispostequal = VarLocMap.equal (fun bp1 bp2 -> 
			begin match (bp1, bp2)  with
			|((b1, p1), (b2, p2)) -> 
				if (p1=p2) && (check_src_base_type b1 b2) then true
				else false
			| _ -> false  
			end ) gpost1 gpost2 in
			(* For functions lower bounds should be equal *)
			(ispreequal && ispostequal && (p1 = p2) && (VarSet.equal u1 u2))
  | BtInt, BtInt -> true
  | BtBool, BtBool -> true
  | BtCond, BtCond -> true
  | BtString, BtString -> true
  | BtArray (n1, lt1), BtArray (n2, lt2) -> if n1 = n2 then check_src_base_type (fst lt1) (fst lt2)
					    else false
  | BtPair (bp11, bp12), BtPair (bp21, bp22) -> let fsteq = check_src_base_type bp11 bp21 in
						let sndeq = check_src_base_type bp12 bp22 in
						if fsteq && sndeq then true
						else false
  | _ ,_ -> false (* int, bool, cond *)

(* Check if base types are same. What about rho? 
   Ignore rho and policy for comparison 
*)
let rec check_enc_base_type b1 b2 = match (b1, b2) with 
  | EBtRef (rho1, lt1), EBtRef (rho2, lt2) -> check_enc_base_type (fst lt1) (fst lt2)
  | EBtFunc (rho1, gencpre1, kpre1, p1, u1, gencpost1, kpost1), EBtFunc (rho2, gencpre2, kpre2, p2, u2, gencpost2, kpost2) -> 
		      let ispreequal = VarLocMap.equal (fun bp1 bp2 -> 
			begin match (bp1, bp2)  with
			|((b1, p1), (b2, p2)) -> 
				if (p1 =p2) && (check_enc_base_type b1 b2) then true
				else false
			| _ -> false  
			end) gencpre1 gencpre2 in
		      let ispostequal = VarLocMap.equal (fun bp1 bp2 -> 
			begin match (bp1, bp2)  with
			|((b1, p1), (b2, p2)) -> 
				if (p1=p2) && (check_enc_base_type b1 b2) then true
				else false
			| _ -> false  
			end ) gencpost1 gencpost2 in
			(* For functions lower bounds should be equal *)
			(ispreequal && ispostequal && (p1 = p2) && (VarSet.equal u1 u2))
  | EBtInt, EBtInt -> true
  | EBtBool, EBtBool -> true
  | EBtCond rho1, EBtCond rho2 -> true
  | EBtString, EBtString -> true
  | EBtArray (mu1, n1, lt1), EBtArray (mu2, n2, lt2) -> if n1 = n2 then check_enc_base_type (fst lt1) (fst lt2)
							else false
  | EBtPair (bp11, bp12), EBtPair (bp21, bp22) -> let fsteq = check_enc_base_type bp11 bp21 in
						let sndeq = check_enc_base_type bp12 bp22 in
						if fsteq && sndeq then true
						else false
  | _ ,_ -> false (* int, bool, cond *)
(* ---------- FRESH TYPE VARIABLES ---------- *)
let tvar_cell = ref 1

(* [next_tid ()] generates a fresh type variable *)
let next_tid () : var =
  let x = !tvar_cell in
  let s = "x" ^ string_of_int x in
  incr tvar_cell;  s


let next_kvar() : var =
   let x = !tvar_cell in
   let s = "x" ^ string_of_int x in
   let _ = incr tvar_cell in
 	s

let gen_killset():killset = 
   let n = number_of_enclaves in
   let rec loop k counter = 
		if counter !=0 then 
			loop (k@[next_kvar()]) (counter-1) 
			 else
				k
	in 
   loop [] n

(* [next_tvar ()] generates a fresh type variable *)
let next_tvar () : mode =
  let x = !tvar_cell in
  let s = "x" ^ string_of_int x in
  let _ = incr tvar_cell in
  (* Generate a list of boolean variables indicating the enclave id *)
  let eidvarlist = gen_killset () in
  ModeVar (s, eidvarlist)

let rec flattenseq s = match s with
|Seq s1 -> s1
| _   -> [s]

(* Returns true when all registers all low *)
let check_typing_context_reg_low (genc1:enccontext) = 
  VarLocMap.for_all (fun key value -> begin match key with
				| Reg x -> begin match (snd value) with
						| Low -> true
						| _ -> false
					   end
				| _ -> true
				end) genc1

let rec countCondConstraints (c:constr2) =
	  let rec outerloop c2 num_constraints =
          	let a, b = Constr2.choose c2 in
          	let c2' = Constr2.remove (a,b) c2 in
	   	let constraints_per_row = 1  in
		let totalconstraints = constraints_per_row + num_constraints in
                if (Constr2.is_empty c2') then totalconstraints else outerloop c2' totalconstraints 
         in
         if (Constr2.is_empty c) then 0 else outerloop c 0

(* Get list of all pre and post killed enclaves *)
let  get_pre_post_killset = function
|TSeq(pc, srcgamma,setu,srcgamma', s,mu,gamma, k, delta, tstmtlistpair, gamma', k') -> 
		let tstmtlist = fst (List.split tstmtlistpair) in
		let rec loop killlist tstmtlist = 
			begin match tstmtlist with
			| [] -> killlist 
			| TSkip(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, gamma', k')::tail
			| TSetcnd(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, gamma', k')::tail 
			| TAssign (pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k')::tail 
			| TDeclassify(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k')::tail
			| TUpdate(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k')::tail
			| TOut(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k')::tail 
			| TIf(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, _, gamma', k')::tail 
			| TWhile(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k')::tail
			| TCall(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _,  gamma', k')::tail->
				 let klist' = 	killlist@[(k,k')] in
				 loop klist' tail
			end in
 		loop [] tstmtlist 
| TSkip(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, gamma', k')
| TSetcnd(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, gamma', k')
| TAssign (pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k')
| TDeclassify(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k')
| TUpdate(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k')
| TOut(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k')
| TIf(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, _, gamma', k')
| TWhile(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k')
| TCall(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _,  gamma', k')->
		[(k, k')]

let get_killed_enclaves_list = function
|TSeq(pc, srcgamma,setu,srcgamma', s,mu,gamma, k, delta, tstmtlistpair, gamma', k') -> 
		snd (List.split tstmtlistpair)
| TSkip(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, gamma', k')
| TSetcnd(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, gamma', k')
| TAssign (pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k')
| TDeclassify(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k')
| TUpdate(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k')
| TOut(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k')
| TIf(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, _, gamma', k')
| TWhile(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k')
| TCall(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _,  gamma', k')->
			[]
