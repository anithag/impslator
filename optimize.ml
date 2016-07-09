open Helper
open Ast
open Proplogic

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


let gen_kill_cost counter wcost p1 p2 = match (p1, p2) with
 |(k1, k1'), (k2, k2') -> let rec loop k2 k1' wcost = begin match (k2, k1') with
				|[], [] -> wcost 
				|(xs2::tail2), (xs1::tail1) -> (* xs2 - xs1 *)
								let tmp = PPlus (PMonoterm (counter, (Mono xs2)), wcost) in
								let tmp' = PMinus (PMonoterm (counter, (Mono xs1)), tmp) in
								 loop tail2 tail1 tmp'
			  end in
			 loop k2 k1' wcost
								 

let rec gen_critical_window_objective wcost tstmt = 
 let klist = get_pre_post_killset tstmt in
 let rec get_window_cost klist wcost counter = begin match klist with
			|[] -> wcost
			|(k1, k1')::(k2, k2')::tail -> 	
				let wcost' = gen_kill_cost counter wcost (k1, k1') (k2, k2') in
				get_window_cost ((k2,k2')::tail) wcost' (counter+1)	
			|(k, k')::[] -> wcost
	end in
	get_window_cost klist wcost 1

