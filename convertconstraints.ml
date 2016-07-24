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
					   mu1 =1 /\ eidlist1[i]=0 /\ eidlist1[i+1]= 1 -> eidlist2[i] = 0 /\ eidlist[i+1] =1 
					   mu1 =1 /\ eidlist1[i]=1 /\ eidlist1[i+1]= 0 -> eidlist2[i] = 1 /\ eidlist[i+1] =0 
					   mu2 =1 /\ eidlist2[i]=1 /\ eidlist2[i+1] = 0 -> eidlist1[i] = 1 /\ eidlist1[i+1] = 0
					   mu2 =1 /\ eidlist2[i]=0 /\ eidlist2[i+1] = 1 -> eidlist1[i] = 0 /\ eidlist1[i+1] = 1
					*)
					let eidlst1 = get_mode_eidlist muvar1 in
					let eidlst2 = get_mode_eidlist muvar2 in 
					let rec loop c2 pre1 pre2 = function
					  |[], [] -> c2
					  | xs1::tail1, xs2::tail2 ->   
								let rec innerloop condlst1 condlst2 pretail1 pretail2 = begin match (pretail1, pretail2) with 
									|[], [] -> (condlst1, condlst2)
									|ps1::ptail1, ps2::ptail2 -> 
												 let condlst1' = (condlst1@[Eidcond(ps1,0)]) in
												 let condlst2' = (condlst2@[Eidcond(ps2,0)]) in
								   
												 innerloop condlst1' condlst2' ptail1 ptail2
									end in
								let (condlst1, condlst2) = innerloop [Eidcond(xs1, 1)] [Eidcond(xs2, 1)] (pre1@tail1) (pre2@tail2) in
								let rec addsingleconstraint c2 condlst2  = begin match condlst2 with
									|[] -> c2
									|c::ctail ->
										let c2' = Constr2.add  (Dnfclause ([Modecond(mu1,1)]@condlst1), c) c2 in 
										addsingleconstraint c2' ctail
									end in
								let c2' = addsingleconstraint c2  condlst2 in
								loop c2' (pre1@[xs1]) (pre2@[xs2]) (tail1, tail2)
					in
					let c4 = loop c3'' [] [] (eidlst1, eidlst2) in
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
					   mu1 =1 /\ eidlist1[i]=0 /\ eidlist1[i+1]= 1 -> eidlist2[i] = 0 /\ eidlist[i+1] =1 
					   mu1 =1 /\ eidlist1[i]=1 /\ eidlist1[i+1]= 0 -> eidlist2[i] = 1 /\ eidlist[i+1] =0 
					   mu2 =1 /\ eidlist2[i]=1 /\ eidlist2[i+1] = 0 -> eidlist1[i] = 1 /\ eidlist1[i+1] = 0
					   mu2 =1 /\ eidlist2[i]=0 /\ eidlist2[i+1] = 1 -> eidlist1[i] = 0 /\ eidlist1[i+1] = 1
					*)
					let eidlst1 = get_mode_eidlist muvar1 in
					let eidlst2 = get_mode_eidlist muvar2 in 
					let rec loop c2 pre1 pre2 = function
					  |[], [] -> c2
					  | xs1::tail1, xs2::tail2 ->   
								let rec innerloop condlst1 condlst2 pretail1 pretail2 = begin match (pretail1, pretail2) with 
									|[], [] -> (condlst1, condlst2)
									|ps1::ptail1, ps2::ptail2 -> 
												 let condlst1' = (condlst1@[Eidcond(ps1,0)]) in
												 let condlst2' = (condlst2@[Eidcond(ps2,0)]) in
								   
												 innerloop condlst1' condlst2' ptail1 ptail2
									end in
								let (condlst1, condlst2) = innerloop [Eidcond(xs1, 1)] [Eidcond(xs2, 1)] (pre1@tail1) (pre2@tail2) in
								let rec addsingleconstraint c2 condlst2  = begin match condlst2 with
									|[] -> c2
									|c::ctail ->
										let c2' = Constr2.add  (Dnfclause ([Modecond(mu1,1)]@condlst1), c) c2 in 
										addsingleconstraint c2' ctail
									end in
								let c2' = addsingleconstraint c2  condlst2 in
								loop c2' (pre1@[xs1]) (pre2@[xs2]) (tail1, tail2)
					in
					let c4 = loop c2' [] [] (eidlst1, eidlst2) in
					(c1, c4)

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
					
| ModeEqimpliesNoKill(muvar1,muvar2, k) (* μ1=μ2 /\ μ1=1 /\ μ2=1  -> k = Ø *) ->
					let mu1 = get_mode_var muvar1 in
					let mu2 = get_mode_var muvar2 in

					let eidlst1 = get_mode_eidlist muvar1 in
					let eidlst2 = get_mode_eidlist muvar2 in 

					(* μ1=μ2 /\ μ1=1 /\ μ2= 1-> k1[i] = 0 
					 *)
					let rec loop c2 k = begin match k with
					| [] -> c2
					| xs3::ktail3 -> 
							let condlst = ([Modecond(mu1,1)]@[Modecond(mu2,1)]) in
							let rec innerloop c3 pre1 pre2 eidlst1 eidlst2 = begin match (eidlst1, eidlst2) with
					 			|[],[]-> c3 
					  			|xs1::ktail1, xs2::ktail2 -> 
									let rec innerloop2 condlst pretail1 pretail2 = begin match (pretail1, pretail2) with 
										|[], [] -> condlst
										|ps1::ptail1, ps2::ptail2 -> 
												 let condlst' = (condlst@[Eidcond(ps1,0);Eidcond(ps2,0)]) in
												 innerloop2 condlst' ptail1 ptail2
									end in
									let condlst' = innerloop2 (condlst@[Eidcond(xs1, 1);Eidcond(xs2,1)]) (pre1@ktail1) (pre2@ktail2) in
									let c4 = Constr2.add  (Dnfclause condlst', Eidcond(xs3, 0)) c3 in 
									innerloop c4 (pre1@[xs1]) (pre2@[xs2]) ktail1 ktail2 
							end in 
							let c4 = innerloop c2 [] []  eidlst1 eidlst2 in
							loop c4 ktail3 
					end in
					let c5 = loop c2 k in
					(c1, c5)

| KillUnion(k1, k2, k3) 		(* K1 = K' U K'' *) ->
					(* k1[i] = 0 -> k2[i]=0 /\ k3[i] = 0
					   k2[i] = 0 /\ k3[i] = 0 -> k1[i] = 0 
					   k2[i] = 1 -> k1[i] = 1
					   k3[i] = 1 -> k1[i] = 1 
					*)
					let rec loop c2 = function
					  |[], [], [] -> c2
					  | xs1::tail1, xs2::tail2, xs3::tail3 -> 
								let c2' = Constr2.add  (Dnfclause ([Eidcond(xs2,0)]@[Eidcond(xs3, 0)]), Eidcond(xs1, 0)) c2 in 
								let c2'' = Constr2.add  (Eidcond(xs1, 0), Dnfclause ([Eidcond(xs2,0)]@[Eidcond(xs3, 0)])) c2' in 
								let c3 = Constr2.add  (Eidcond(xs2, 1), Eidcond(xs1,1)) c2'' in 
								let c3' = Constr2.add  (Eidcond(xs3, 1), Eidcond(xs1,1)) c3 in 
									loop c3' (tail1, tail2, tail3)
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
					
| EnclaveExitimpliesModeEq(muvar1, muvar2) 	(* ~isVarLowContext -> μi = μi+1 *) ->
					(* Revisit: making this same as mu1 = mu2 *)
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

| EnclaveExitimpliesKill(muvar,k) 	(* ~isVarLowContext -> K'' = Ø *) ->
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

| Enclaveid muvar				->	
					(* Ensures that if enclave mode is not normal, then atleast one of the identifier is set*)
					let mu = get_mode_var muvar in
					let eidlst = get_mode_eidlist muvar in
					let rec loop1 dnflist = function
					| [] -> dnflist
					| xs1::tail -> 
						       loop1 (dnflist@[Eidcond (xs1, 0)]) tail
					in
					let dnflist = loop1 [] eidlst in
					let c3 = Constr2.add ((Dnfclause dnflist), Modecond (mu,0))  c2 in 
					
					(* Ensures that only one identifier is set *)
					let rec loop2 pre c4 = function
					| [] -> c4
					| xs1::tail -> let rec innerloop c5 = function
							|[] -> c5
							|xs2::tail'->
									let c5' = Constr2.add (Dnfclause ([Modecond(mu,1)]@[Eidcond (xs1, 1)]), Eidcond (xs2,0)) c5 in
									innerloop c5' tail'
							in 
							let c6 = innerloop c4 (pre@tail) in
							loop2 (pre@[xs1]) c6 tail
					in 
					let c7 = loop2 [] c3 eidlst in
					(c1, c7)

 |UsedEnclave (k, mulist) 		->
						(* k[i] = 1 <-> \/ mulist[i] = 1 *)
						(* /\ mulist[i] =0 <-> k[i] = 0 *)
						let rec loop c index = function
						| [] -> c
						| xs::tail -> let rec innerloop cond_li = function
								| [] -> cond_li
								|muxs::mutail -> let eidlist = get_mode_eidlist muxs in
										innerloop (cond_li@[Eidcond(List.nth eidlist index, 0)]) mutail
								in
							     let cond_li = innerloop [] mulist in
							     let c' = Constr2.add (Dnfclause cond_li, Eidcond (List.nth k index, 0)) c in 

							     let c'' = Constr2.add (Eidcond (List.nth k index, 0), Dnfclause cond_li) c' in 
							     loop c'' (index+1) tail
						in
						let c3 = loop c2 0 k in
						(c1, c3) 

let rec convertconstraints c1 c2 tconstrset =
    if (TConstraints.is_empty tconstrset) then
			(c1, c2)
    else
	let tconstr = TConstraints.choose tconstrset in
	let c3, c4 = convertconstr c1 c2 tconstr in
	convertconstraints c3 c4  (TConstraints.remove tconstr tconstrset)

