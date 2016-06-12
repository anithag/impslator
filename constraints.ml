open Ast
open Helper

exception TypeError 
exception ModeError
exception TranslationError of string
exception TypeNotFoundError 
exception UnificationError
exception UnimplementedError of string
exception EmptySeqError
exception JoinError of string

(* Return join of policies in policy lattice *)
let join p = match p with 
  |Low, High
  |High, Low -> High
  |_, Top
  |Top, _ -> Top
  |Low, Low -> Low
  |High,High -> High
  |Erase(l, c, h), Low -> Erase(l, c, h)
  |Low, Erase(Low,c,High)
  |Erase(Low,c,High), Low -> Erase(Low, c, High)
  |Low, Erase(l1,c,top)
  |Erase(l1,c,top), Low -> Erase(l1, c, top)
  |Erase(Low, c1, High), Erase(Low, c2, High) -> High
  | High, Erase(High, c, top)
  | Erase(High, c, top), High -> Erase(High, c, top)
  |Erase(_, c1, Top), Erase(_, c2, Top) -> Top
  |_ -> raise (JoinError "Not Exhaustive")

let rec join_src_tau = function
 |((BtInt, p1), (BtInt, p2)) -> (BtInt, join (p1, p2))
 |((BtBool, p1), (BtBool, p2)) -> (BtBool, join (p1, p2))
 |((BtCond, p1), (BtCond, p2)) -> (BtCond, join (p1, p2))
 |((BtRef (lt1), p1), (BtRef (lt2), p2)) -> (* Assume that rho1 = rho2 constraint will be generated *)
						(* FIXME: Reference types are invariant. Compare lt1 and lt2 here and emit error if they are unequal *)
						 (BtRef lt1, join (p1, p2))
 |((BtFunc(gpre1, p1, u1, gpost1), q1), (BtFunc (gpre2, p2, u2, gpost2), q2)) ->
							(* FIXME: Not implementing function subtyping for now *) 
							(* gpre1 = gpre2 and gpost1 = gpost2*)
							(BtFunc (join_src_context (gpre1, gpre2), p1, u1, 
							join_src_context (gpost1, gpost2)), join (q1, q2))

(* Only modes should differ, remaining should be same *)
and join_src_context (g1, g2) = 
  let g' = VarLocMap.merge (fun key a b -> begin match (a,b) with
 				| (Some a, Some b) -> Some (join_src_tau (a,b)) 
				| (None, Some b) -> raise (JoinError " ") 
				| (Some a, None) -> raise (JoinError " ")
				end) g1 g2
  in g'
 
let rec join_enc_tau = function
 |((EBtInt, p1), (EBtInt, p2)) -> (EBtInt, join (p1, p2))
 |((EBtBool, p1), (EBtBool, p2)) -> (EBtBool, join (p1, p2))
 |((EBtCond mu1, p1), (EBtCond mu2, p2)) -> (EBtCond mu1, join (p1, p2))(* FIXME: Assume that mu1 = mu2 constraint will be generated *)
 |((EBtRef (mu1, lt1), p1), (EBtRef (mu2, lt2), p2)) -> (* FIXME: References are invariant. Compare lt1 and lt2 and emit error if they are unequal *)
							 (EBtRef (mu1, lt1), join (p1, p2))
 |((EBtFunc(mu1, gencpre1,kpre1, p1, u1, gencpost1, kpost1), q1), (EBtFunc (mu2, gencpre2, kpre2, p2, u2, gencpost2, kpost2), q2)) ->
							(* FIXME: Not implementing function subtyping for now *) 
							(* gencpre1 = gencpre2 and gencpost1 = gencpost2, kpre1=kpre2; kpost1 = kpost2   *)
							(EBtFunc (mu1, join_enc_context (gencpre1, gencpre2), kpre1, p1, u1, 
							join_enc_context (gencpost1, gencpost2), kpost1), join (q1, q2))

(* Only modes should differ, remaining should be same *)
and join_enc_context (g1, g2) = 
  let g' = VarLocMap.merge (fun key a b -> begin match (a,b) with
 				| (Some a, Some b) -> Some (join_enc_tau (a,b)) 
				| (None, Some b) -> raise (JoinError "")
				| (Some a, None) -> raise (JoinError "") 
				end) g1 g2
  in g'
 
let rec get_exp_type (g:context) (e:exp) : labeltype =
  match e with
   | Var x -> (try VarLocMap.find (Reg x) g with Not_found -> raise TypeNotFoundError)
   | Loc l -> (try VarLocMap.find (Mem l) g with Not_found -> (try VarLocMap.find (Arr l) g with Not_found -> raise TypeNotFoundError))
   | Lam(gpre, p,u, gpost,q, s) -> (BtFunc(gpre, p,u, gpost), q)
   | Constant n -> (BtInt, Low)
   | Literal  s -> (BtString, Low)
   | Tuple (e1, e2) -> (BtPair (fst (get_exp_type g e1), fst (get_exp_type g e2)), join (snd (get_exp_type g e1), snd (get_exp_type g e2)))
   | True    -> (BtBool, Low)
   | False -> (BtBool, Low)
   | Eq(e1, e2)
   | Neq(e1, e2) -> (BtBool, join (snd (get_exp_type g e1), snd (get_exp_type g e2)))
   | Plus(e1, e2) 
   | Modulo(e1, e2) -> (BtInt, join (snd (get_exp_type g e1), snd (get_exp_type g e2)))
   | Fst e   -> (get_exp_type g e)
   | Snd e   -> (get_exp_type g e)
   | Isunset x -> (BtBool, Low)
   | Index (e1, i) -> begin match (get_exp_type g e1) with
		  | (BtArray (s, lt), p) -> (BtRef lt, p)
		  | _  -> raise TypeError
		 end
   | Deref e1   -> begin match (get_exp_type g e1) with
		  | ((BtRef lt), p) -> (fst lt, join ((snd lt), p))
		  | _  -> raise TypeError
		 end
 
let rec get_exp_label lt = (snd lt)
		
let rec translatetype (s:labeltype)  = 
	match s with
	| (BtInt, p ) -> ((EBtInt, p), TConstraints.empty)
	| (BtBool, p) -> ((EBtBool, p), TConstraints.empty)
	| (BtString, p) -> ((EBtString, p), TConstraints.empty)
	| (BtPair (b1, b2), p) -> ((EBtPair (fst(fst (translatetype (b1,p))), fst(fst (translatetype (b2, p)))), p), TConstraints.empty)
	| (BtCond, p) -> let mu = next_tvar () in ((EBtCond mu, p), (TConstraints.add (Enclaveid mu) TConstraints.empty))
	| (BtArray (size, b), p) -> let mu = next_tvar () in
			 let (b', c) = (translatetype b) in
			((EBtArray(mu, size, b'), p), (TConstraints.add (Enclaveid mu) c))
	| (BtRef b, p)-> let mu = next_tvar () in
			 let (b', c) = (translatetype b) in
			((EBtRef(mu, b'), p), (TConstraints.add (Enclaveid mu) c))
        | (BtFunc(gpre, p, u, gpost), q) -> let mu = next_tvar () in
			let kpre = gen_killset () in
			let kpost = gen_killset () in
			let tmpc = TConstraints.empty in
			(* Convert gpre and gpost*)
			(* translatetype returns a tuple of labeledtype and constraints *)
			let gencpretmp = (VarLocMap.map (fun a -> translatetype a ) gpre) in
			let gencposttmp = (VarLocMap.map (fun a -> translatetype a) gpost) in
			let gencpre  = (VarLocMap.map (fun a -> fst a ) gencpretmp) in
			let gencpost = (VarLocMap.map (fun a -> fst a) gencposttmp) in

			(* update constraints *)
			let tmpc' = (VarLocMap.fold (fun key a c -> (TConstraints.union (snd a) c)) gencpretmp tmpc) in 
			let tmpc'' = (VarLocMap.fold (fun key a c -> (TConstraints.union (snd a) c)) gencposttmp tmpc') in 
			 ((EBtFunc(mu, gencpre, kpre, p, u, gencpost, kpost), q), tmpc'')
and translategamma (g:context) = 
	let genctmp = (VarLocMap.map (fun a -> translatetype a) g) in
	let genc = (VarLocMap.map (fun a -> fst a) genctmp) in
	let c = (VarLocMap.fold (fun key a c -> (TConstraints.union (snd a) c)) genctmp TConstraints.empty) in 
	 (* enumerate all location bindings and generate constraints on delta *)
	let gencloc = (VarLocMap.filter (fun key a -> begin match key with
					| Reg x -> false
					| Mem l -> true
					| Arr l -> true
					end ) genc) in
	let allloc = VarLocMap.bindings gencloc in
	let rec loop loclist c delta = begin match loclist with
		|[] -> (c, delta)
		|(Mem l, (EBtRef(mu, (_, Low)), _))::tail -> loop tail c  delta
		|(Mem l, (EBtRef(mu, (_, _)), _))::tail -> let delta' = VarLocMap.add (Mem l) mu delta in
							    loop tail (TConstraints.add (ModeisN(mu, 1)) c) delta'
		|(Arr l, (EBtArray(mu, i, (_, Low)), _))::tail -> loop tail c  delta
		|(Arr l, (EBtArray(mu, i, (_, _)), _))::tail -> let delta' = VarLocMap.add (Arr l) mu delta in
							    loop tail (TConstraints.add (ModeisN(mu, 1)) c) delta'
		| _::tail -> raise (TranslationError "Only Mem/Array bindings are allowed")
		end in 
	let (c1, delta) = loop allloc c (VarLocMap.empty) in
	(c1, delta, genc)
 
 
let rec get_enc_exp_type (genc:enccontext) (e:encexp) : enclabeltype =
  match e with
   | EVar x  -> (try VarLocMap.find (Reg x) genc with Not_found -> raise TypeNotFoundError)
   | ELoc(mu, l) -> (try VarLocMap.find (Mem l) genc with Not_found -> (try VarLocMap.find (Arr l) genc with Not_found -> raise TypeNotFoundError))
   | ELam(mu, gpre, kpre, p,u, gpost, kpost, q,s) -> (EBtFunc(mu,gpre, kpre, p,u, gpost, kpost), q) 
   | EConstant n -> (EBtInt, Low)
   | ELiteral s -> (EBtString, Low)
   | ETuple(e1, e2) 	-> (EBtPair (fst (get_enc_exp_type genc e1), fst (get_enc_exp_type genc e2)), join (snd (get_enc_exp_type genc e1), snd (get_enc_exp_type genc e2)))
   | ETrue     -> (EBtBool, Low)
   | EFalse  -> (EBtBool, Low)
   | EEq(e1, e2) 
   | ENeq(e1, e2) -> (EBtBool, join (snd (get_enc_exp_type genc e1), snd (get_enc_exp_type genc e2)))
   | EPlus(e1, e2) 
   | EModulo(e1, e2) -> (EBtInt, join (snd (get_enc_exp_type genc e1 ), snd (get_enc_exp_type genc e2)))
   | EFst e   -> (get_enc_exp_type genc e)
   | ESnd e   -> (get_enc_exp_type genc e)
   | EIsunset x -> (EBtBool, Low)
   | EIndex (mu, e1, i) -> begin match (get_enc_exp_type genc e1) with
		  | (EBtArray (mu, s, b), p) -> (EBtRef (mu,b), p)
		  | _  -> raise TypeError
		 end
   | EDeref  e   -> begin match (get_enc_exp_type genc e) with
		  | (EBtRef(_, lt), p) -> (fst lt, join ((snd lt), p))
		  | _  -> raise TypeError
		 end
 
let rec get_enc_exp_label lt = (snd lt)
		

(* Given a src statement, compute the resulting typing context after the execution of statement *)
let rec src_flow_sensitive_type_infer (pc:policy) (g:context) = function
    |Assign(x,e)-> 
		      let srctype = get_exp_type  g e in
		      let srcvarlabtype = join (pc, (get_exp_label srctype)) in
		      let g1 = VarLocMap.add (Reg x) (fst srctype, srcvarlabtype) g in
		      g1
    |Declassify(x,e) -> 
		      let srctype = get_exp_type  g e in
		      let g1 = VarLocMap.add (Reg x) (fst srctype, Low) g in
		      g1
    |Update(e1, e2) -> g
    |Seq(s1, s2)  ->  let g1 = src_flow_sensitive_type_infer pc g s1 in
		      let g2 = src_flow_sensitive_type_infer pc g1 s2 in
		      g2 
    |Set x	-> g
    |Skip -> g
    |If(e, s1, s2) ->   
		      let pc' = join (get_exp_label (get_exp_type g e), pc) in
    		      let g1 = src_flow_sensitive_type_infer pc' g s1 in
		      let g2 = src_flow_sensitive_type_infer pc' g s2 in
		      let g' = VarLocMap.merge (fun key bp1 bp2 -> 
			begin match (bp1, bp2)  with
			|(Some (b1, p1), Some (b2, p2)) -> 
				if (check_src_base_type b1 b2 ) then Some (b1, join(p1, p2))
				else raise (TranslationError "Join of source contexts not possible. Different base types.")
			| _ -> raise (TranslationError "Join of source contexts not possible. Domain of contexts is not same.") 
			end ) g1 g2
			in g'
    |While(e, s) -> (* Compute Fixpoint *)
		    let rec compute_fixpoint s gi'  = 
		    	 let pc' = join (get_exp_label (get_exp_type gi' e), pc) in
			 let gi'' = src_flow_sensitive_type_infer pc' gi' s in
		         let gn = VarLocMap.merge (fun key bp1 bp2 -> 
						begin match (bp1, bp2)  with
						|(Some (b1, p1), Some (b2, p2)) -> 
								if (check_src_base_type b1 b2 ) then Some (b1, join(p1,p2))
								else raise (TranslationError "Join of source contexts not possible. Different base types.")
						| _ -> raise (TranslationError "Join of source contexts not possible. Domain of contexts is not same.") 
						end ) g gi''
			in 
			 if (VarLocMap.equal (fun a b -> if a = b then true else false) gi' gi'') then
			 	gn
			 else 
				compute_fixpoint s  gn
		     in compute_fixpoint s g

    |Call e ->  let srctype = get_exp_type g e in
		let gpost = get_src_postcontext srctype in
		(* G_out(x) = G_post(x) if x is in Dom(G_post)
			    = G(x) o.w *)
		let gout = VarLocMap.merge (fun key left right -> begin match (left, right) with
							| Some x, Some y -> left
							| None, right -> right 
							| left, None  -> None (* error *)
							end) gpost g
		in
		gout
		 
		
    |Output(x, e) -> g
    | _  -> raise (UnimplementedError "src flow sensitive typing not implemented for this statement")


let rec enc_flow_sensitive_type_infer (pc:policy) (genc:enccontext) = function
    |EAssign(x, e)-> 
		      let enctype = get_enc_exp_type  genc e in
		      let encvarlabtype = join (pc, (get_enc_exp_label enctype)) in
		      let genc1 = VarLocMap.add (Reg x) (fst enctype, encvarlabtype) genc in
		      genc1
    |EDeclassify(x, e) -> 
		      let enctype = get_enc_exp_type  genc e in
		      let genc1 = VarLocMap.add (Reg x) (fst enctype, Low) genc in
		      genc1
    |EUpdate( e1, e2) -> genc
    |ESeq( s1, s2)  ->  let g1 = enc_flow_sensitive_type_infer pc genc s1 in
		            let g2 = enc_flow_sensitive_type_infer pc g1 s2 in
		      	    g2 
    |EESeq(slist)  -> let rec seq_flow_sensitive genc = function
				|[] -> genc
				|s::tail ->
			    		let genc' = enc_flow_sensitive_type_infer pc genc s in
					seq_flow_sensitive genc' tail
			   in seq_flow_sensitive genc slist

    |ESet(x)	-> genc
    |ESkip -> genc
    |EIf(e, s1, s2) ->   
		      let pc' = get_enc_exp_label (get_enc_exp_type genc e) in
    		      let g1 = enc_flow_sensitive_type_infer pc' genc s1 in
		      let g2 = enc_flow_sensitive_type_infer pc' genc s2 in
		      let g' = VarLocMap.merge (fun key bp1 bp2 -> 
			begin match (bp1, bp2)  with
			|(Some (b1, p1), Some (b2, p2)) -> 
				if (check_enc_base_type b1 b2 ) then Some (b1, join(p1, p2))
				else raise (TranslationError "Join of target contexts not possible. Different base types.")
			| _ -> raise (TranslationError "Join of target contexts not possible. Domain of contexts is not same.") 
			end ) g1 g2
			in g'
    |EWhile(e, s) -> (* Compute Fixpoint *)
		    let rec compute_fixpoint s gi'  = 
		    	 let pc' = join (get_enc_exp_label (get_enc_exp_type gi' e), pc) in
			 let gi'' = enc_flow_sensitive_type_infer pc' gi' s in
		         let gn = VarLocMap.merge (fun key bp1 bp2 -> 
						begin match (bp1, bp2)  with
						|(Some (b1, p1), Some (b2, p2)) -> 
								if (check_enc_base_type b1 b2 ) then Some (b1, join(p1, p2))
								else raise (TranslationError "Join of enclave contexts not possible. Different base types.")
						| _ -> raise (TranslationError "Join of enclave contexts not possible. Domain of contexts is not same.") 
						end ) genc gi''
			in 
			 if (VarLocMap.equal (fun a b -> if a = b then true else false) gi' gi'') then
			 	gn
			 else 
				compute_fixpoint s  gn
		     in compute_fixpoint s genc
    |ECall (e) ->  let enctype = get_enc_exp_type genc e in
			let gencpost = get_enc_postcontext enctype in
			(* Genc_out(x) = Genc_post(x) if x is in Dom(Genc_post)
			    = Genc(x) o.w *)
			let gencout = VarLocMap.merge (fun key left right -> begin match (left, right) with
							| Some x, Some y -> left
							| None, right -> right 
							| left, None  -> None (* error *)
							end) gencpost genc
			in
			gencout
    |EOutput(x, e) -> genc
    | _  -> raise (UnimplementedError "Enclave flow sensitive typing not implemented for this statement")

let get_translated_stmt_delta = function
| TSkip(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, gamma', k')
| TSetcnd(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, gamma', k')
| TAssign (pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k')
| TDeclassify(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k')
| TUpdate(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k')
| TOut(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k') -> delta
| TSeq(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, tlist, gamma', k') -> delta
| TIf(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, _, gamma', k') -> delta
| TWhile(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, encexp, tbody, gamma', k') -> delta
| TCall(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, tlamexp,  gamma', k')->  delta

let get_translated_stmt_src_postgamma = function
| TSkip(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, gamma', k')
| TSetcnd(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, gamma', k')
| TAssign (pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k')
| TDeclassify(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k')
| TUpdate(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k')
| TOut(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k') -> srcgamma'
| TSeq(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, tlist, gamma', k') -> srcgamma'
| TIf(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, encexp, ttrue, tfalse, gamma', k') -> srcgamma'
| TWhile(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, encexp, tbody, gamma', k') -> srcgamma'
| TCall(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, tlamexp,  gamma', k')->  srcgamma'

let get_translated_stmt_enc_pregamma = function
| TSkip(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, gamma', k')
| TSetcnd(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, gamma', k')
| TAssign (pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k')
| TDeclassify(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k')
| TUpdate(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k')
| TOut(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k') -> gamma
| TSeq(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, tlist, gamma', k') -> gamma
| TIf(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, encexp, ttrue, tfalse, gamma', k') -> gamma
| TWhile(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, encexp, tbody, gamma', k') -> gamma
| TCall(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, tlamexp,  gamma', k')->  gamma

let get_translated_stmt_enc_postgamma = function
| TSkip(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, gamma', k')
| TSetcnd(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, gamma', k')
| TAssign (pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k')
| TDeclassify(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k')
| TUpdate(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k')
| TOut(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k') -> gamma'
| TSeq(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, tlist, gamma', k') -> gamma'
| TIf(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, encexp, ttrue, tfalse, gamma', k') -> gamma'
| TWhile(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, encexp, tbody, gamma', k') -> gamma'
| TCall(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, tlamexp,  gamma', k')->  gamma'

let get_translated_stmt_enc_prekillset = function
| TSkip(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, gamma', k')
| TSetcnd(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, gamma', k')
| TAssign (pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k')
| TDeclassify(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k')
| TUpdate(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k')
| TOut(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k') -> k
| TSeq(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, tlist, gamma', k') -> k
| TIf(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, encexp, ttrue, tfalse, gamma', k') -> k
| TWhile(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, encexp, tbody, gamma', k') -> k

let get_translated_stmt_enc_postkillset = function
| TSkip(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, gamma', k')
| TSetcnd(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, gamma', k')
| TAssign (pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k')
| TDeclassify(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k')
| TUpdate(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k')
| TOut(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k') -> k'
| TSeq(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, tlist, gamma', k') -> k'
| TIf(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, encexp, ttrue, tfalse, gamma', k') -> k'
| TWhile(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, encexp, tbody, gamma', k') -> k'
| TCall(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, tlamexp,  gamma', k')->  k'

let get_translated_stmt_mode = function
| TSkip(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, gamma', k')
| TSetcnd(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, gamma', k')
| TAssign (pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k')
| TDeclassify(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k')
| TUpdate(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k')
| TOut(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k')
| TSeq(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, gamma', k') 
| TIf(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, _, gamma', k') 
| TWhile(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k') 
| TCall(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _,  gamma', k')-> mu

let get_translated_stmt_postcontext = function
| TSkip(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, gamma', k')
| TSetcnd(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, gamma', k')
| TAssign (pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k')
| TDeclassify(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k')
| TUpdate(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k')
| TOut(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k')
| TIf(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, _, gamma', k') 
| TWhile(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k') 
| TCall(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _,  gamma', k')-> (pc, setu, mu, gamma, k, delta, gamma', k')

let get_translated_exp_gamma = function
| TExp(_,e,_,_, g, _,_, _) 
| TLamExp(_,e,_,_, g, _,_, _) -> g

let get_translated_exp_delta = function
| TExp(_,e,_,_, g, delta,_, enctype) 
| TLamExp(_,e,_,_, g, delta,_, enctype) -> delta


let get_translated_exp_type = function
| TExp(_,e,_,_, g, _,_, enctype)
| TLamExp(_,e,_,_, g, _,_, enctype) -> enctype


let  rec get_translated_seq_stmt tstmt = 
  let tstmtlist = begin match tstmt with
		|TSeq(pc, srcgamma,setu,srcgamma', s,mu,gamma, k, delta, tstmtlist, gamma', k') -> tstmtlist
		| _   -> raise (TranslationError "Expected Seq translation")
		end in
  let rec loop  estmtlist tstmtlist = begin match tstmtlist with
	| [] -> estmtlist
	| TSkip(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, encs, gamma', k')::tail -> loop (estmtlist@[encs]) tail
	| TSetcnd(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, cnd, gamma', k')::tail -> loop (estmtlist@[ESet(cnd)]) tail
	| TAssign (pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, x, texp, gamma', k')::tail -> loop (estmtlist@[EAssign (x, (get_translated_exp texp))]) tail
	| TDeclassify(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, x, texp, gamma', k')::tail -> loop (estmtlist@[EDeclassify (x, (get_translated_exp texp))]) tail
	| TUpdate(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, texp1, texp2, gamma', k')::tail -> loop (estmtlist@[EUpdate ((get_translated_exp texp1), (get_translated_exp texp2))]) tail
	| TOut(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, ch, texp, gamma', k')::tail -> loop (estmtlist@[EOutput(ch, (get_translated_exp texp))]) tail
	| TIf(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, encexp, ttrue, tfalse, gamma', k')::tail -> let enctruestmt = (get_translated_seq_stmt ttrue) in
											      	      let encfalsestmt = (get_translated_seq_stmt tfalse) in	
											      	      loop (estmtlist@[EIf(encexp, enctruestmt, encfalsestmt)]) tail 
	| TWhile(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, encexp, tbody, gamma', k')::tail -> let encbody = (get_translated_seq_stmt tbody) in
												loop (estmtlist@[EWhile (encexp, encbody)]) tail
	| TCall(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, tlamexp,  gamma', k')::tail -> 
												loop (estmtlist@[ECall(get_translated_exp tlamexp)]) tail
 end in 
let estmtlist = loop [] tstmtlist in
(EESeq estmtlist)

and get_translated_stmt = function
| TSkip(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, encs, gamma', k')-> encs
| TSetcnd(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, cnd, gamma', k')-> ESet(cnd)
| TAssign (pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, x, texp, gamma', k')-> EAssign (x, (get_translated_exp texp))
| TDeclassify(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, x, texp, gamma', k')-> EDeclassify (x, (get_translated_exp texp))
| TUpdate(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, texp1, texp2, gamma', k')-> EUpdate((get_translated_exp texp1), (get_translated_exp texp2))
| TOut(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, ch, texp, gamma', k')-> EOutput(ch, (get_translated_exp texp))
| TIf(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, encexp, ttrue, tfalse, gamma', k') -> let enctruestmt = get_translated_seq_stmt ttrue in
											      let encfalsestmt = get_translated_seq_stmt tfalse in	
											      EIf(encexp, enctruestmt, encfalsestmt) 
| TWhile(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, encexp, tbody, gamma', k') -> let encbody = get_translated_seq_stmt tbody in
												EWhile(encexp, encbody)
| TCall(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, tlamexp,  gamma', k')-> ECall(get_translated_exp tlamexp)

and get_translated_exp = function
| TExp(_,e,_,_, g, _,ee, _) -> ee
| TLamExp(_,e,_,_, g, _,tstmt, _) -> let encs = get_translated_seq_stmt tstmt in
				     let (pc, setu, mu, gamma, k, delta, gamma', k') = get_translated_stmt_postcontext tstmt in
				     let q = Low in
				     ELam(mu, gamma,k, pc, setu, gamma', k', q, encs)   
 
let rec gen_constraints_stmt pc srcgamma setu s mu gamma k delta = match s with
 | Assign (v,e) -> let b = get_exp_type srcgamma e in 
		 let c1, texp = gen_constraints_exp srcgamma e b mu gamma delta  in
		 let gammatmp = get_translated_exp_gamma texp in
		 let enclt = get_translated_exp_type texp in
		 let varlabtype = join (pc, (get_enc_exp_label enclt)) in
		 let ence = get_translated_exp texp in
		 let encs =  EAssign (v, ence) in 
		 let c2 = if labnotlow varlabtype then
				TConstraints.add (ModeisN (mu, 1)) c1 
			  else
				c1 in
		 (* update gamma *)
		 let srcgamma' = src_flow_sensitive_type_infer pc srcgamma s in
		 let gamma' =  enc_flow_sensitive_type_infer pc gammatmp encs in
		 let tstmt = TAssign(pc,srcgamma,setu,srcgamma',s,mu,gamma, k, delta, v, texp, gamma', k) in
		 (c2, tstmt)
 | Declassify (v,e) -> let b = get_exp_type srcgamma e in 
		 let c1, texp = gen_constraints_exp srcgamma e b mu gamma delta  in
		 let gammatmp = get_translated_exp_gamma texp in
		 let enclt = get_translated_exp_type texp in
		 let varlabtype = Low in
		 let ence = get_translated_exp texp in
		 let encs =  EDeclassify(v, ence) in 
		 (* update gamma *)
		 let srcgamma' = src_flow_sensitive_type_infer pc srcgamma s in
		 let gamma' =  enc_flow_sensitive_type_infer pc gammatmp encs in
		 let tstmt = TDeclassify(pc,srcgamma,setu,srcgamma',s,mu,gamma, k, delta, v, texp, gamma', k) in
		 (c1, tstmt)
 | Update(e1,e2) -> let b1 = get_exp_type srcgamma e1 in 
		 let c1, texp1 = gen_constraints_exp srcgamma e1 b1 mu gamma delta  in
		 let gammatmp1 = get_translated_exp_gamma texp1 in
		 let b2 = get_exp_type srcgamma e2 in 
		 let c2, texp2 = gen_constraints_exp srcgamma e2 b2 mu gammatmp1 delta  in
		 let gammatmp2 = get_translated_exp_gamma texp2 in
		 let ence1 = get_translated_exp texp1 in
		 let ence2 = get_translated_exp texp2 in
		 let encs =  EUpdate(ence1, ence2) in 
		 (* update gamma *)
		 let srcgamma' = src_flow_sensitive_type_infer pc srcgamma s in
		 let gamma' =  enc_flow_sensitive_type_infer pc gammatmp2 encs in
		 let tstmt = TUpdate(pc,srcgamma,setu,srcgamma',s,mu,gamma, k, delta, texp1, texp2, gamma', k) in
		 (TConstraints.union c1 c2, tstmt)
 |Seq(s1, s2)  -> let seqlist = flattenseq s in
			let rec seqloop c1 mui g genc ki tstmtlist = function
			| [] -> (c1, g, genc, ki, tstmtlist)
			| xs::tail -> 
				    let  c2, tstmt1 = gen_constraints_stmt pc g setu xs mui genc ki delta in
				    let  g' = get_translated_stmt_src_postgamma tstmt1 in
				    let genc' = get_translated_stmt_enc_postgamma tstmt1 in
				    let k' = get_translated_stmt_enc_postkillset tstmt1 in
				    let k'' = gen_killset () in

				    (* K'' ∩ K ' = Ø *)
				    let c3 = TConstraints.add (KillIntersectEmpty(k'', k')) c2 in

				    let kj  = gen_killset () in

				    (* Kj = K' U K'' *)
				    let c4 = TConstraints.add (KillUnion(kj, k', k'')) c3 in

				    (* Check if genc' has any high registers. If yes, raise error. Translation not possible*)
				    let allreglow = check_typing_context_reg_low genc' in

				    if not (List.length tail = 0) then
				    	let muj = next_tvar () in
					let c4' = TConstraints.add (Enclaveid muj) c4 in

					(* μ = N -> μi = μ *)
					let c5 = TConstraints.add (ModenotNimpliesEq(mu, mui)) c4' in


					(* μ = N -> K'' = Ø *)
					let c6 = TConstraints.add (ModenotNimpliesNoKill(mu, k'')) c5 in

					let c8 = if (not allreglow) then 
							(* ~isVarLowContext -> μi = N ∨ μi = μi+1 *)
							let c7 = TConstraints.add (EnclaveExitimpliesModeEq(mui,muj)) c6 in

							(* ~isVarLowContext -> μi = N ∨ K'' = Ø *)
							TConstraints.add (EnclaveExitimpliesKill(mui, k'')) c7 
						 else 
							c6
					in
		
				     	seqloop (TConstraints.union c1 c8) muj g' genc' kj (tstmtlist@[tstmt1]) tail

				    (* Last instruction in the sequence *)
				     else
					if (not allreglow) then 
						raise (TranslationError "Registers may contain secrets when exiting enclave.")
					else
				     		seqloop (TConstraints.union c1 c4) mui g' genc' kj (tstmtlist@[tstmt1])  tail
		     in
		     let mu1 = next_tvar () in
		     let c', srcgamma', gamma', k', tstmtlist = seqloop (TConstraints.add (Enclaveid mu1) TConstraints.empty) mu1 srcgamma gamma k [] seqlist in
		     let tseq = TSeq(pc, srcgamma,setu,srcgamma', s,mu,gamma, k, delta, tstmtlist, gamma', k') in
		     (c', tseq)
 |If (e, s1, s2) ->let b = get_exp_type srcgamma e in 
		   let c, texp = gen_constraints_exp srcgamma e b mu gamma delta  in
		   let encgamma = get_translated_exp_gamma texp in
		   let mu1 = next_tvar () in
		   let  c1, tstmt1 = gen_constraints_stmt pc srcgamma setu s1 mu1 encgamma k delta in
	    	   let k1 = get_translated_stmt_enc_postkillset tstmt1 in
		   (* let genc1 = get_translated_stmt_enc_postgamma tstmt1 in *)
		   let mu2 = next_tvar () in
		   let  c2, tstmt2 = gen_constraints_stmt pc srcgamma setu s2 mu2 encgamma k delta in
	    	   let k2 = get_translated_stmt_enc_postkillset tstmt2 in
		   (* let genc2 = get_translated_stmt_enc_postgamma tstmt2 in *)
		   let ence = get_translated_exp texp in
		   let es1 = get_translated_seq_stmt tstmt1 in
		   let es2 = get_translated_seq_stmt tstmt2 in
		   let encs =  EIf(ence, es1, es2) in 
		   let srcgamma' = src_flow_sensitive_type_infer pc srcgamma s in
		   let gamma' =  enc_flow_sensitive_type_infer pc encgamma encs in

		   let allreglow = check_typing_context_reg_low gamma' in
		   let c3 = TConstraints.union c c1 in
		   let c4 = TConstraints.union c2 c3 in
		   let c5 = TConstraints.add (KillEq (k1, k2)) c4 in
		   let c6 = if not allreglow then
				TConstraints.add (ModeisN (mu, 1)) c5
			    else
				c5 in
		   let enclt = get_translated_exp_type texp in
		   let c7 = if labnotlow (snd enclt) then
				TConstraints.add (ModeisN (mu, 1)) c5
			    else
				c6 in
		   let k' = k1 in (* k1 or k2 does not matter, because k1 = k2 *)
		   let tstmt = TIf(pc,srcgamma,setu,srcgamma',s,mu,gamma, k, delta, ence, tstmt1, tstmt2, gamma', k') in
 		   (c7, tstmt)
 |While (e, s1) ->let b = get_exp_type srcgamma e in 
		   let c, texp = gen_constraints_exp srcgamma e b mu gamma delta  in
		   let encgamma = get_translated_exp_gamma texp in
		   let mu1 = next_tvar () in
		   let  c1, tstmt1 = gen_constraints_stmt pc srcgamma setu s1 mu1 encgamma k delta in
	    	   let k1 = get_translated_stmt_enc_postkillset tstmt1 in

		   let ence = get_translated_exp texp in
		   let es1 = get_translated_seq_stmt tstmt1 in
		   let encs =  EWhile(ence, es1) in 
		   let srcgamma' = src_flow_sensitive_type_infer pc srcgamma s in
		   let gamma' =  enc_flow_sensitive_type_infer pc encgamma encs in

		   let allreglow = check_typing_context_reg_low gamma' in
		   let c2 = TConstraints.union c c1 in
		   let c3 = TConstraints.add (KillEq (k, k1)) c2 in
		   let c4 = if not allreglow then
				TConstraints.add (ModeisN (mu, 1)) c3
			    else
				c3 in
		   let enclt = get_translated_exp_type texp in
		   let c5 = if labnotlow (snd enclt) then
				TConstraints.add (ModeisN (mu, 1)) c4
			    else
				c4 in
		   let tstmt = TWhile(pc,srcgamma,setu,srcgamma',s,mu,gamma, k, delta, ence, tstmt1, gamma', k1) in
 		   (c5, tstmt)
 |Call(e) 	->let b = get_exp_type srcgamma e in 
		  let c, texp = gen_constraints_exp srcgamma e b mu gamma delta  in
		  let encgamma = get_translated_exp_gamma texp in
		  let enctype = get_translated_exp_type texp in
		  let encgammaplus = get_enc_postcontext enctype in
		  let prekill = get_prekillset enctype in
		  let postkill = get_postkillset enctype in
		  let c1 = TConstraints.add (KillEq (k, prekill)) c in

		  let ence = get_translated_exp texp in
		  let encs =  ECall(ence) in 
		  (* FIXME: Prepare gammaout = encgammaplus U encgamma *)
		  let srcgamma' = src_flow_sensitive_type_infer pc srcgamma s in
		  let gamma' =  enc_flow_sensitive_type_infer pc encgamma encs in

		  let tstmt = TCall(pc,srcgamma,setu,srcgamma',s,mu,gamma, k, delta, texp, gamma', postkill) in
		  (c1, tstmt)
 | Skip 	-> let encs = ESkip in
		  let tstmt = TSkip(pc,srcgamma,setu,srcgamma,s,mu,gamma, k, delta, encs, gamma, k) in
		   (TConstraints.empty, tstmt)
 | Set x 	-> 
		  let tstmt = TSetcnd(pc,srcgamma,setu,srcgamma,s,mu,gamma, k, delta, x, gamma, k) in
		   (TConstraints.empty, tstmt)
 | Output(ell, e) ->
 		 let b = get_exp_type srcgamma e in 
		 let c1, texp1 = gen_constraints_exp srcgamma e b mu gamma delta  in
		 let gammatmp1 = get_translated_exp_gamma texp1 in
		 let ence = get_translated_exp texp1 in
		 let encs =  EOutput(ell, ence) in 
		 (* update gamma *)
		 let srcgamma' = src_flow_sensitive_type_infer pc srcgamma s in
		 let gamma' =  enc_flow_sensitive_type_infer pc gammatmp1 encs in
		 let tstmt = TOut(pc,srcgamma,setu,srcgamma',s,mu,gamma, k, delta, ell, texp1, gamma', k) in
		 (TConstraints.union c1 TConstraints.empty, tstmt)
		   
 

and gen_constraints_exp srcgamma e srctype mu gamma delta= match e with 
   | Var x     ->  
		    let (enctype, gamma', c) = if (VarLocMap.mem (Reg x) gamma) then 
		    				(VarLocMap.find (Reg x) gamma, gamma, TConstraints.empty) 
		    			else
						let (enctype, c) = translatetype srctype in
				  		(enctype, VarLocMap.add (Reg x) enctype gamma, c)
				 in 
		    (* let mu' = get_mode enctype in *)
		    let ence = EVar x in
		    let texp = TExp(srcgamma,e,srctype, mu,gamma',delta,ence,enctype) in
		    (c, texp)
  | Constant n   -> 
		  let (enctype, c) = translatetype srctype in
		  let ence = EConstant n in
		  let texp = TExp(srcgamma,e,srctype, mu,gamma,delta,ence,enctype) in
		   (c, texp)
  | Literal s   -> 
		  let (enctype, c) = translatetype srctype in
		  let ence = ELiteral s in
		  let texp = TExp(srcgamma,e,srctype, mu,gamma,delta,ence,enctype) in
		   (c, texp)
  | Tuple (e1, e2)->
		 let b1 = get_exp_type srcgamma e1 in 
		 let c1, texp1 = gen_constraints_exp srcgamma e1 b1 mu gamma delta  in

		 (* Translate e1 *)
		 let ence1 = get_translated_exp texp1 in
		 let gamma1 = get_translated_exp_gamma texp1 in

		 let b2 = get_exp_type srcgamma e2 in 
		 let c2, texp2 = gen_constraints_exp srcgamma e2 b2 mu gamma1 delta  in

		 (* Translate e2 *)
		 let ence2 = get_translated_exp texp2 in
		 let gamma2 = get_translated_exp_gamma texp2 in

		 let ence = ETuple (ence1, ence2) in
		 let enctype = get_enc_exp_type gamma2 ence in 

		 let texp = TExp(srcgamma,e,srctype, mu,gamma2,delta,ence,enctype) in
		 (TConstraints.union c1 c2, texp)
 | Fst e'	->
		 let b = get_exp_type srcgamma e' in 
		 let c, texp = gen_constraints_exp srcgamma e' b mu gamma delta  in

		 (* Translate e' *)
		 let ence' = get_translated_exp texp in
		 let gamma' = get_translated_exp_gamma texp in

		 (* REMOVE this: delta does not change *)
		 let delta' = get_translated_exp_delta texp in
		 let enclt = get_translated_exp_type texp in
		
		 let ence = (EFst ence') in
		 let enctype = get_enc_exp_type gamma' ence in 

		 let texp = TExp(srcgamma,e,srctype, mu,gamma',delta',ence,enctype) in
		  (c, texp)
 | Snd e'	->  
		 let b = get_exp_type srcgamma e' in 
		 let c, texp = gen_constraints_exp srcgamma e' b mu gamma delta  in

		 (* Translate e' *)
		 let ence' = get_translated_exp texp in
		 let gamma' = get_translated_exp_gamma texp in

		 (* REMOVE this: delta does not change *)
		 let delta' = get_translated_exp_delta texp in
		 let enclt = get_translated_exp_type texp in
		
		 let ence = (ESnd ence') in
		 let enctype = get_enc_exp_type gamma' ence in 

		 let texp = TExp(srcgamma,e,srctype, mu,gamma',delta',ence,enctype) in
		  (c, texp)
 | Loc l        -> 
		    (* bindings should exist: Either Ref or Array *)
		    let enctype = (try VarLocMap.find (Mem l) gamma with Not_found -> (VarLocMap.find (Arr l) gamma)) in
		    let mu' = get_mode enctype in
		    let ence = ELoc(mu', l) in
		    (* gamma and delta need not be updated *)
		    let texp = TExp(srcgamma,e,srctype, mu,gamma,delta,ence,enctype) in
		    (TConstraints.empty, texp)
 |Index (e', i) -> 
		    let b = get_exp_type srcgamma e' in 
		    let c1, texp' = gen_constraints_exp srcgamma e' b mu gamma delta  in
		    let ence' = get_translated_exp texp' in
		    let gamma' = get_translated_exp_gamma texp' in

		    let enctype' = get_enc_exp_type gamma' ence' in
		    let mu' = get_mode enctype' in
		    let ence = EIndex(mu', ence', i) in
		    let enctype = get_enc_exp_type gamma' ence in 

		    (* gamma and delta need not be updated *)
		    let texp = TExp(srcgamma,e,srctype, mu,gamma,delta,ence,enctype) in
		    (TConstraints.empty, texp)
 | Deref e'     ->
		 let b = get_exp_type srcgamma e' in 
		 let c1, texp = gen_constraints_exp srcgamma e' b mu gamma delta  in

		 (* Translate e' *)
		 let ence' = get_translated_exp texp in
		 let gamma' = get_translated_exp_gamma texp in

		 (* REMOVE this: delta does not change *)
		 let delta' = get_translated_exp_delta texp in
		 let enclt = get_translated_exp_type texp in
		 let mu' = get_mode enclt  in
		
		 (* μ' != N -> μ = μ' *)
		 let c2 = TConstraints.add (ModenotNimpliesEq(mu', mu)) c1 in
		 let ence = (EDeref ence') in
		 let enctype = get_enc_exp_type gamma' ence in 

		 let texp = TExp(srcgamma,e,srctype, mu,gamma',delta',ence,enctype) in
		  (c2, texp)
 |Isunset x ->
		    (* srctype is (cond ref, low) *)
		    let (enctype, gamma', c) = if (VarLocMap.mem (Reg x) gamma) then 
		    				(VarLocMap.find (Reg x) gamma, gamma, TConstraints.empty) 
		    		else
						let (enctype, c) = translatetype srctype in
				  		(enctype, VarLocMap.add (Reg x) enctype gamma, c)
				 in 
		    let mu' = get_mode enctype in
		    let delta' = VarLocMap.add (Reg x) mu' delta in
		    let ence = EIsunset x in
		    let texp = TExp(srcgamma,e,srctype, mu,gamma',delta',ence,enctype) in

		    let c1 = TConstraints.add (ModenotNimpliesEq(mu', mu)) c in
		    (c1, texp)
 | Lam(gpre, p, u, gpost,q, s) -> 
		    let (enctype, c) = translatetype srctype in
		    let (m', gencpre, kpre, p, u, gencpost, kpost) = invert_encfunctype enctype in
		    let  c1, tstmt = gen_constraints_stmt p gpre u s m' gencpre kpre delta in
		    let delta' = get_translated_stmt_delta tstmt in
		    let texp = TLamExp(srcgamma,e,srctype, mu,gamma,delta',tstmt,enctype) in

		    let c1' = TConstraints.union c1 c in
		    let c2 = TConstraints.add (ModeEqual(mu,m')) c1' in
		    let allreglow = check_typing_context_reg_low gencpost in
		    let c3 = if (not allreglow) then
				(TConstraints.add (ModeisN(m',1)) c2)
			     else
				c2
		    in (c3, texp)
 |True		-> (TConstraints.empty, TExp(srcgamma,e,srctype, mu,gamma,delta,ETrue, (EBtBool, Low)))
 |False		-> (TConstraints.empty, TExp(srcgamma,e,srctype, mu,gamma,delta,EFalse, (EBtBool, Low)))
		 
 |Plus (e1, e2) ->
		 let b1 = get_exp_type srcgamma e1 in 
		 let c1, texp1 = gen_constraints_exp srcgamma e1 b1 mu gamma delta  in

		 (* Translate e1 *)
		 let ence1 = get_translated_exp texp1 in
		 let gamma1 = get_translated_exp_gamma texp1 in

		 let b2 = get_exp_type srcgamma e2 in 
		 let c2, texp2 = gen_constraints_exp srcgamma e2 b2 mu gamma1 delta  in

		 (* Translate e2 *)
		 let ence2 = get_translated_exp texp2 in
		 let gamma2 = get_translated_exp_gamma texp2 in

		 let ence = EPlus (ence1, ence2) in
		 let enctype = get_enc_exp_type gamma2 ence in 

		 let texp = TExp(srcgamma,e,srctype, mu,gamma2,delta,ence,enctype) in
		 (TConstraints.union c1 c2, texp)
 |Modulo (e1, e2) ->
		 let b1 = get_exp_type srcgamma e1 in 
		 let c1, texp1 = gen_constraints_exp srcgamma e1 b1 mu gamma delta  in

		 (* Translate e1 *)
		 let ence1 = get_translated_exp texp1 in
		 let gamma1 = get_translated_exp_gamma texp1 in

		 let b2 = get_exp_type srcgamma e2 in 
		 let c2, texp2 = gen_constraints_exp srcgamma e2 b2 mu gamma1 delta  in

		 (* Translate e2 *)
		 let ence2 = get_translated_exp texp2 in
		 let gamma2 = get_translated_exp_gamma texp2 in

		 let ence = EModulo (ence1, ence2) in
		 let enctype = get_enc_exp_type gamma2 ence in 

		 let texp = TExp(srcgamma,e,srctype, mu,gamma2,delta,ence,enctype) in
		 (TConstraints.union c1 c2, texp)
 |Eq (e1, e2) ->
		 let b1 = get_exp_type srcgamma e1 in 
		 let c1, texp1 = gen_constraints_exp srcgamma e1 b1 mu gamma delta  in

		 (* Translate e1 *)
		 let ence1 = get_translated_exp texp1 in
		 let gamma1 = get_translated_exp_gamma texp1 in

		 let b2 = get_exp_type srcgamma e2 in 
		 let c2, texp2 = gen_constraints_exp srcgamma e2 b2 mu gamma1 delta  in

		 (* Translate e2 *)
		 let ence2 = get_translated_exp texp2 in
		 let gamma2 = get_translated_exp_gamma texp2 in

		 let ence = EEq (ence1, ence2) in
		 let enctype = get_enc_exp_type gamma2 ence in 

		 let texp = TExp(srcgamma,e,srctype, mu,gamma2,delta,ence,enctype) in
		 (TConstraints.union c1 c2, texp)
 |Neq (e1, e2) ->
		 let b1 = get_exp_type srcgamma e1 in 
		 let c1, texp1 = gen_constraints_exp srcgamma e1 b1 mu gamma delta  in

		 (* Translate e1 *)
		 let ence1 = get_translated_exp texp1 in
		 let gamma1 = get_translated_exp_gamma texp1 in

		 let b2 = get_exp_type srcgamma e2 in 
		 let c2, texp2 = gen_constraints_exp srcgamma e2 b2 mu gamma1 delta  in

		 (* Translate e2 *)
		 let ence2 = get_translated_exp texp2 in
		 let gamma2 = get_translated_exp_gamma texp2 in

		 let ence = ENeq (ence1, ence2) in
		 let enctype = get_enc_exp_type gamma2 ence in 

		 let texp = TExp(srcgamma,e,srctype, mu,gamma2,delta,ence,enctype) in
		 (TConstraints.union c1 c2, texp)

and gen_constraints_type (s1: enclabeltype) (s2:enclabeltype) = 
   match (s1, s2) with
   |(EBtRef(m1,s1'), p), (EBtRef( m2, s2'), q) -> let t1 = gen_constraints_type s1' s2' in  [(m1, m2)]@t1 
							(* FIXME: equate gencpre1 and gencpre2; likewise equate gencpost1 and gencpost2 *)
   |(EBtFunc(m1, gencpre1,kpre1, p1, u1, gencpost1, kpost1), q1), (EBtFunc(m2, gencpre2, kpre2, p2, u2, gencpost2, kpost2), q2) -> 
						let rec gen_constraints_type_for_context genc1 genc2 c =
							let c' = if (not (VarLocMap.is_empty genc1)) && (not (VarLocMap.is_empty genc2)) then
									let (key, value1) = VarLocMap.choose genc1 in
									let value2 = (try VarLocMap.find key genc2 with Not_found -> 
										raise (TranslationError " Error in generating type constraints for functions ")) in
									let c' = gen_constraints_type value1 value2 in
									let genc1', genc2' = (VarLocMap.remove key genc1, VarLocMap.remove key genc2) in
									gen_constraints_type_for_context genc1' genc2' c@c'
								else
									c
							in c'
						in  
						let c1 = gen_constraints_type_for_context gencpre1 gencpre2 [(m1, m2)] in
						let c2 = gen_constraints_type_for_context gencpost1 gencpost2 c1 in
						c2
   | _ -> []
     
