open Helper
open Ast
open Proplogic

exception ObjectiveError of string

let rec gen_tcb_objective tcbcost = function
|TSeq(pc, srcgamma,setu,srcgamma', s,mu,gamma, k, delta, tstmtlistpair, gamma', k') -> 
  		let tstmtlist = fst (List.split tstmtlistpair) in
		let rec loop tcbcost tstmtlist = 
			begin match tstmtlist with
			| [] -> tcbcost 
			| TSkip(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, gamma', k')::tail
			| TSetcnd(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, gamma', k')::tail -> 
					let tcbcost' = (PPlus ((PMonoterm (1, (Mono (get_mode_var mu)))),tcbcost)) in
					loop tcbcost' tail

			| TAssign (pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, texp, gamma', k')::tail 
			| TDeclassify(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, texp, gamma', k')::tail
			| TUpdate(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, texp, gamma', k')::tail
			| TOut(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, texp, gamma', k')::tail ->
					let tcbcost' = (PPlus ((PMonoterm (1, (Mono (get_mode_var mu)))), (gen_tcb_exp_objective tcbcost texp))) in
					loop tcbcost' tail
			| TIf(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, encexp, ttrue, tfalse, gamma', k')::tail -> 
					let tcbcost1 = (PPlus (PMonoterm (1, (Mono (get_mode_var mu))), (gen_tcb_objective tcbcost ttrue))) in
					let tcbcost' = (gen_tcb_objective tcbcost1 tfalse) in
					loop tcbcost' tail
			| TWhile(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, encexp, tbody, gamma', k')::tail ->
					let tcbcost'= (PPlus (PMonoterm (1, (Mono (get_mode_var mu))), (gen_tcb_objective tcbcost tbody))) in
					loop tcbcost' tail
			| TCall(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, texp,  gamma', k')::tail->
					let tcbcost' = (PPlus (PMonoterm (1, (Mono (get_mode_var mu))), (gen_tcb_exp_objective tcbcost texp))) in
					loop tcbcost' tail
			end in
		loop tcbcost tstmtlist  	
| TSkip(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, gamma', k')
| TSetcnd(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, gamma', k')->(PPlus ((PMonoterm (1, (Mono (get_mode_var mu)))),tcbcost))
| TAssign (pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, texp, gamma', k')
| TDeclassify(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, texp, gamma', k')
| TUpdate(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, texp, gamma', k')
| TOut(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, texp, gamma', k')->
									(PPlus (PMonoterm (1, (Mono (get_mode_var mu))), (gen_tcb_exp_objective tcbcost texp)))
| TIf(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, encexp, ttrue, tfalse, gamma', k')-> 
									let tcbcost1 = (PPlus (PMonoterm (1, (Mono (get_mode_var mu))), (gen_tcb_objective tcbcost ttrue))) in
									(gen_tcb_objective tcbcost1 tfalse)
| TWhile(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, encexp, tbody, gamma', k')->
									(PPlus (PMonoterm (1, (Mono (get_mode_var mu))), (gen_tcb_objective tcbcost tbody)))
| TCall(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, texp,  gamma', k')->
									(PPlus (PMonoterm (1, (Mono (get_mode_var mu))), (gen_tcb_exp_objective tcbcost texp))) 

and gen_tcb_exp_objective tcbcost texp = match texp with
|TExp(srcgamma,e,srctype, mu,gamma',delta,ence,enctype) -> tcbcost (* 0 cost for expressions *)
|TLamExp(srcgamma,e,srctype, mu,gamma,delta',tstmt,enctype) -> gen_tcb_objective tcbcost tstmt 


(* Minimize the window of vulnerability by maximizing the kill sets.
   Let K1, K2....Kn be form a lattice (L, <) with  partial order K1 < {K2, K3} < ...< Kn.
   Let level(Ki) be the level of element Ki in lattice
   Let the elements of set Ki = {ki1, ki2,...kim} with kij = 0/1 indicating the set membership.
   Cost contributed by each set Ki = Σ_j=1...m (level(i) * kij)
   Total Cost = Σ_i=1...n Σ_j=1...m (i * kij) 
   Thus maximizing the killsets involves 
	involves minimizing the total cost
 *)
		
let gen_kill_cost_old counter wcost p1 p2 = match (p1, p2) with
 |(k1, k1'), (k2, k2') -> let rec loop k2 k1' wcost = begin match (k2, k1') with
				|[], [] -> wcost 
				|(xs2::tail2), (xs1::tail1) -> (* xs2 - xs1 *)
								let tmp = PPlus (PMonoterm (counter, (Mono xs2)), wcost) in
								let tmp' = PMinus (PMonoterm (counter, (Mono xs1)), tmp) in
								 loop tail2 tail1 tmp'
			  end in
			 loop k2 k1' wcost
								 
let gen_kill_cost counter kcost k = 
  let rec loop k kcost = begin match k with
	| [] -> kcost
	|(xs::tail) -> 
		let tmpcost = PPlus (PMonoterm (counter, (Mono xs)), kcost) in
		 loop tail tmpcost
	  end in
 loop k kcost
								 

let rec gen_critical_window_objective counter kcost tstmt = match tstmt with
|TSeq(pc, srcgamma,setu,srcgamma', s,mu,gamma, k, delta, tstmtlistpair, gamma', k') -> 
		let rec loop counter kcost tstmtlistpair = 
			begin match tstmtlistpair with
			| [] -> (counter, kcost) 
			| (TSkip(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, gamma', k'),k'')::tail
			| (TSetcnd(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, gamma', k'),k'')::tail  
			| (TAssign (pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k'), k'')::tail 
			| (TDeclassify(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k'), k'')::tail
			| (TUpdate(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _, gamma', k'),k'')::tail
			| (TOut(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, _, _ , gamma', k'),k'')::tail ->
					let kcost' = gen_kill_cost counter kcost k'' in
					loop (counter+1) kcost' tail
			| (TIf(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, encexp, ttrue, tfalse, gamma', k'),k'')::tail -> 
					let (counter1, kcost1) = gen_critical_window_objective counter kcost ttrue in
					let (counter2, kcost2) = gen_critical_window_objective counter kcost1 tfalse in
					let counter' = if counter1 > counter2 then counter1 else counter2 in
					let kcost' = gen_kill_cost counter' kcost2 k'' in
					loop (counter'+1) kcost' tail
			| (TWhile(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, encexp, tbody, gamma', k'),k'')::tail ->
					let (counter', kcost') =  gen_critical_window_objective counter kcost tbody in 
					let kcost'' = gen_kill_cost counter' kcost' k'' in
					loop (counter'+1) kcost'' tail
			| (TCall(pc, srcgamma,setu,srcgamma',s,mu,gamma, k, delta, texp,  gamma', k'),k'')::tail->
					(*FIXME: Should thread through the functions? *)
					let kcost' = gen_kill_cost counter kcost k'' in
					loop (counter+1) kcost' tail
			end in
		loop counter kcost tstmtlistpair  	
| _ -> raise (ObjectiveError "Only Sequence is supported for now")

