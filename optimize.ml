open Helper
open Ast
open Proplogic

let rec gen_tcb_objective tcbcost = function
|TSeq(pc, srcgamma,setu,srcgamma', s,mu,gamma, k, delta, tstmtlist, gamma', k') -> 
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

