open Ast

exception HelperError of string


let number_of_enclaves = 10

let get_mode_var = function
|ModeVar(mu1, l) -> mu1
| _   -> raise (HelperError "Expected Mode variable")

let get_mode_eidlist = function
|ModeVar(mu1, l) -> l
| _   -> raise (HelperError "Expected Mode variable")

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
  (* Generate a list of boolean variables indicating the enclave id *)
  let eidvarlist = gen_killset () in
  ModeVar (s, eidvarlist)

let rec flattenseq s = match s with
|Seq(c1, c2) -> flattenseq c1 @ flattenseq c2
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

