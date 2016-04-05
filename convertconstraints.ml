open Proplogic
open Helper
open Ast

let rec convertconstr c1 c2 = function
| ModeisN(muvar, v)			(* μ = 1/0 *) -> 
					let mu = get_mode_var muvar in
					let c1' =	if v = 1 then
								Constr.add (Modecond(mu, 1))  c1 
							else
								Constr.add (Modecond(mu, 0)) c1
					in (c1', c2)

| ModeEqual(muvar1,  muvar2)		(* μ1 = μ2 *) ->
					let mu1 = get_mode_var muvar1 in
					let mu2 = get_mode_var muvar2 in
			                 (* Match on enclave/normal modes *)
					let c2' = Constr2.add (Modecond(mu1, 1), Modecond(mu2, 1)) c2 in
					let c2'' = Constr2.add (Modecond(mu1, 0), Modecond(mu2, 0)) c2' in
					let c3' = Constr2.add (Modecond(mu2, 1), Modecond(mu1, 1)) c2'' in
					let c3'' = Constr2.add (Modecond(mu2, 0), Modecond(mu1, 0)) c3' in

					(* Match on enclave identifiers as well i.e., 
					   mu1 =1 /\ eidlist1[i]=1 -> eidlist2[i] = 1 
					   mu1 =1 /\ eidlist1[i]=0 -> eidlist2[i] = 0 
					   mu2 =1 /\ eidlist2[i]=1 -> eidlist1[i] = 1 
					   mu2 =1 /\ eidlist2[i]=0 -> eidlist1[i] = 0 
					*)
					let eidlst1 = get_mode_eidlist muvar1 in
					let eidlst2 = get_mode_eidlist muvar2 in 
					let rec loop c2 = function
					  |[], [] -> c2
					  | xs1::tail1, xs2::tail2 -> let c2' = Constr2.add  (Dnfclause ([Modecond(mu1,1)]@[Eidcond(xs1, 1)]), Eidcond(xs2, 1)) c2 in 
									let c2'' = Constr2.add  (Dnfclause ([Modecond(mu1,1)]@[Eidcond(xs1, 0)]), Eidcond(xs2, 0)) c2' in 
									let c3 = Constr2.add  (Dnfclause ([Modecond(mu2,1)]@[Eidcond(xs2, 1)]), Eidcond(xs1, 1)) c2'' in 
									let c3' = Constr2.add  (Dnfclause ([Modecond(mu2,1)]@[Eidcond(xs2, 0)]), Eidcond(xs1, 0)) c3 in 
									
									loop c3' (tail1, tail2)
					in 
					let c4 = loop c3''  (eidlst1, eidlst2) in
					(c1, c4)

| ModenotKilled(muvar, k) 		(* μ \not \in K *) ->
					let mu = get_mode_var muvar in

					(* 
					   mu =1 /\ eidlist[i]=1 -> k[i] = 0 
					*)
					let eidlst = get_mode_eidlist muvar in
					let rec loop c2 = function
					  |[], [] -> c2
					  |xs1::tail, xs2::ktail -> let c2' = Constr2.add  (Dnfclause ([Modecond(mu,1)]@[Eidcond(xs1, 1)]), Eidcond(xs2, 0)) c2 in 
									loop c2' (tail, ktail)
					in 
					let c3 = loop c2  (eidlst, k) in
					(c1, c3)

| ModenotNimpliesEq(muvar1, muvar2)   	(* μ1 = 1 -> μ1 = μ2 *) ->
					let mu1 = get_mode_var muvar1 in
					let mu2 = get_mode_var muvar2 in
			                 (* Match on enclave/normal modes *)
					let c2' = Constr2.add (Modecond(mu1, 1), Modecond(mu2, 1)) c2 in

					(* Match on enclave identifiers as well i.e., 
					   mu1 =1 /\ eidlist1[i]=1 -> eidlist2[i] = 1 
					   mu1 =1 /\ eidlist1[i]=0 -> eidlist2[i] = 0 
					   mu1 =1 /\ eidlist2[i]=1 -> eidlist1[i] = 1 
					   mu1 =1 /\ eidlist2[i]=0 -> eidlist1[i] = 0 
					*)
					let eidlst1 = get_mode_eidlist muvar1 in
					let eidlst2 = get_mode_eidlist muvar2 in 
					let rec loop c2 = function
					  |[], [] -> c2
					  | xs1::tail1, xs2::tail2 -> let c2' = Constr2.add  (Dnfclause ([Modecond(mu1,1)]@[Eidcond(xs1, 1)]), Eidcond(xs2, 1)) c2 in 
									let c2'' = Constr2.add  (Dnfclause ([Modecond(mu1,1)]@[Eidcond(xs1, 0)]), Eidcond(xs2, 0)) c2' in 
									let c3 = Constr2.add  (Dnfclause ([Modecond(mu1,1)]@[Eidcond(xs2, 1)]), Eidcond(xs1, 1)) c2'' in 
									let c3' = Constr2.add  (Dnfclause ([Modecond(mu1,1)]@[Eidcond(xs2, 0)]), Eidcond(xs1, 0)) c3 in 

									loop c3' (tail1, tail2)
					in 
					let c3 = loop c2'  (eidlst1, eidlst2) in
					(c1, c3)

| ModenotNimpliesNoKill(muvar,k)  	(* μ = 1 -> K'' = Ø *) ->
					let mu = get_mode_var muvar in
					(* 
					   mu =1 -> k[i] = 0 
					*)
					let rec loop c2 = function
					  |[] -> c2
					  |xs::ktail -> let c2' = Constr2.add  (Modecond(mu,1), Eidcond(xs, 0)) c2 in 
									loop c2'  ktail
					in 
					let c3 = loop c2  k in
					(c1, c3)
					
| KillUnion(k1, k2, k3) 		(* K1 = K' U K'' *) ->
					(* k1[i] = 0 -> k2[i]=0 /\ k3[i] = 0
					   k2[i] = 0 /\ k3[i] = 0 -> k1[i] = 0 
					*)
					let rec loop c2 = function
					  |[], [], [] -> c2
					  | xs1::tail1, xs2::tail2, xs3::tail3 -> 
								let c2' = Constr2.add  (Dnfclause ([Eidcond(xs2,0)]@[Eidcond(xs3, 0)]), Eidcond(xs1, 0)) c2 in 
								let c2'' = Constr2.add  (Eidcond(xs1, 0), Dnfclause ([Eidcond(xs2,0)]@[Eidcond(xs3, 0)])) c2' in 
									loop c2'' (tail1, tail2, tail3)
					in 
					let c3 = loop c2  (k1, k2, k3) in
					(c1, c3)
			
| KillIntersectEmpty(k1, k2) 		(* K1 ∩ K2 = Ø *) ->
					(* 
					   k1[i] =1 -> k2[i] = 0 
					   k2[i] =1 -> k1[i] = 0 
					*)
					let rec loop c2 = function
					  |[],[] -> c2
					  |xs1::tail1, xs2::tail2 -> let c2' = Constr2.add  (Eidcond(xs1,1), Eidcond(xs2, 0)) c2 in 
								     let c2'' = Constr2.add  (Eidcond(xs2,1), Eidcond(xs1, 0)) c2' in 
								     loop c2''  (tail1, tail2)
					in 
					let c3 = loop c2  (k1, k2) in
					(c1, c3)
					
| EnclaveExitimpliesModeEq(muvar1, muvar2) 	(* ~isVarLowContext -> μi = N ∨ μi = μi+1 *) ->
					(* Revisit: making this same as mu1 = m2 *)
					let mu1 = get_mode_var muvar1 in
					let mu2 = get_mode_var muvar2 in
			                 (* Match on enclave/normal modes *)
					let c2' = Constr2.add (Modecond(mu1, 1), Modecond(mu2, 1)) c2 in
					let c2'' = Constr2.add (Modecond(mu1, 0), Modecond(mu2, 0)) c2' in
					let c3' = Constr2.add (Modecond(mu2, 1), Modecond(mu1, 1)) c2'' in
					let c3'' = Constr2.add (Modecond(mu2, 0), Modecond(mu1, 0)) c3' in

					(* Match on enclave identifiers as well i.e., 
					   mu1 =1 /\ eidlist1[i]=1 -> eidlist2[i] = 1 
					   mu1 =1 /\ eidlist1[i]=0 -> eidlist2[i] = 0 
					   mu2 =1 /\ eidlist2[i]=1 -> eidlist1[i] = 1 
					   mu2 =1 /\ eidlist2[i]=0 -> eidlist1[i] = 0 
					*)
					let eidlst1 = get_mode_eidlist muvar1 in
					let eidlst2 = get_mode_eidlist muvar2 in 
					let rec loop c2 = function
					  |[], [] -> c2
					  | xs1::tail1, xs2::tail2 -> let c2' = Constr2.add  (Dnfclause ([Modecond(mu1,1)]@[Eidcond(xs1, 1)]), Eidcond(xs2, 1)) c2 in 
									let c2'' = Constr2.add  (Dnfclause ([Modecond(mu1,1)]@[Eidcond(xs1, 0)]), Eidcond(xs2, 0)) c2' in 
									let c3 = Constr2.add  (Dnfclause ([Modecond(mu2,1)]@[Eidcond(xs2, 1)]), Eidcond(xs1, 1)) c2'' in 
									let c3' = Constr2.add  (Dnfclause ([Modecond(mu2,1)]@[Eidcond(xs2, 0)]), Eidcond(xs1, 0)) c3 in 
									
									loop c3' (tail1, tail2)
					in 
					let c4 = loop c3''  (eidlst1, eidlst2) in
					(c1, c4)

| EnclaveExitimpliesKill(muvar,k) 	(* ~isVarLowContext -> μi = N ∨ K'' = Ø *) ->
					(* Revisit: making this same as k = Ø *)
					let rec loop c1 = function
					  |[] -> c1
					  |xs::ktail -> let c1' = Constr.add  (Eidcond(xs, 0)) c1 in 
									loop c1'  ktail
					in 
					let c3 = loop c1  k in
					(c3, c2)

| KillEq (k1, k2)			(* K1 = K2 *)->
					(* 
					  k1[i]=1 -> k2[i] = 1 
					  k1[i]=0 -> k2[i] = 0 
					  k2[i]=1 -> k1[i] = 1 
					  k2[i]=0 -> k1[i] = 0 
					*)
					let rec loop c2 = function
					  |[], [] -> c2
					  | xs1::tail1, xs2::tail2 -> let c2' = Constr2.add  (Eidcond(xs1, 1), Eidcond(xs2, 1)) c2 in 
									let c2'' = Constr2.add  (Eidcond(xs1, 0), Eidcond(xs2, 0)) c2' in 
									let c3 = Constr2.add  (Eidcond(xs2, 1), Eidcond(xs1, 1)) c2'' in 
									let c3' = Constr2.add  (Eidcond(xs2, 0), Eidcond(xs1, 0)) c3 in 
									
									loop c3' (tail1, tail2)
					in 
					let c3 = loop c2  (k1, k2) in
					(c1, c3)

| Killempty k			      (* μ = Ø *)->
					let rec loop c1 = function
					  |[] -> c1
					  |xs::ktail -> let c1' = Constr.add  (Eidcond(xs, 0)) c1 in 
									loop c1'  ktail
					in 
					let c3 = loop c1  k in
					(c3, c2)

| Enclaveid muvar			->	
					let eidlst = get_mode_eidlist muvar in
					let rec loop c2 = function
					| [] -> c2
					| xs1::tail -> let rec innerloop c3 = function
							|[] -> c3
							|xs2::tail'->
									let c3' = Constr2.add (Modecond (xs1, 1), Modecond (xs2,0)) c3 in
									let c3'' = Constr2.add (Modecond (xs2, 1), Modecond (xs1,0)) c3' in
									innerloop c3'' tail'
							in 
							let c4 = innerloop c2 tail in
							loop c4 tail
					in 
					let c5 = loop c2 eidlst in
					(c1, c5)

let rec convertconstraints c1 c2 tconstrset =
    if (TConstraints.is_empty tconstrset) then
			(c1, c2)
    else
	let tconstr = TConstraints.choose tconstrset in
	let c3, c4 = convertconstr c1 c2 tconstr in
	convertconstraints c3 c4  (TConstraints.remove tconstr tconstrset)

