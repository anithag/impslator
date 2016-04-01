open Ast
open Helper

(* Entry given more cost than trusted code
  sum_j (-(1-rho) rho_i rho_j b_ij)
 = sum_j (-rho_i rho_j d_ij + rho rho_i rho_j b_ij)
 *)
let rec compute_seq_diffencid_cost eslist (rho:mode) (es:encstmt) eidmap eidrevmap fcost = match eslist with
	|[] -> (fcost, eidmap, eidrevmap) 
	|xs1::tail -> 
			let rhoi,rhoj = (getstmtmode es, getstmtmode xs1 )  in
			let (bij, eidmap, eidrevmap)  = if EnclaveidRevMap.mem (rhoi, rhoj) eidrevmap then
					(EnclaveidRevMap.find (rhoi, rhoj) eidrevmap, eidmap, eidrevmap)
				  else
					let bij = next_tid() in
					let tempeidrevmap = EnclaveidRevMap.add (rhoi, rhoj) bij eidrevmap in
					(bij, EnclaveidMap.add bij (rhoi, rhoj) eidmap, EnclaveidRevMap.add (rhoj, rhoi) bij tempeidrevmap)
			in 
			(* Temporary hack - don't use two lookups to update *)
			
 			(* -rho_i rho_j b_ij + rho rho_i rho_j b_ij *)
 			let partialcost = (PMinus ((PMonoterm (1, (Poly ((Mode rho), (Poly ((Mode rhoi), (Poly ((Mode rhoj),(Mono (Eid bij)))))))))), 
								(PMonoterm (1, (Poly ((Mode rhoi), (Poly ((Mode rhoj),(Mono (Eid bij)))))))))) in
			let tpcost = PPlus (fcost, partialcost) in
			compute_seq_diffencid_cost tail rho es eidmap eidrevmap tpcost 


let compute_one_seq_entry_cost (rho:mode) (rhoi:mode) (rhoj:mode) (bij:var) ecost =
			let rho1, rho2 = (rhoi, rhoj)  in
			(* rho_j - rho rho_j *)
			let term1 = (PMinus (PMonoterm (1, (Mono (Mode rho2))), (PMonoterm (1, (Poly ((Mode rho), ((Mono (Mode rho2))))))))) in
			(* rho_j - rho rho_j - rho_i rho_j *)
			let term2 = (PMinus (term1, (PMonoterm (1, (Poly ((Mode rho1), (Mono (Mode rho2)))))))) in
			(* rho_j - rho rho_i+1 - rho_i rho_j + rho rho_i rho_j *)
 			let entrycost = (PPlus (term2, (PMonoterm (1, (Poly ((Mode rho), (Poly ((Mode rho1), (Mono (Mode rho2)))))))))) in
			(* rho_j - rho rho_j - rho_i rho_j + rho rho_i rho_j  + bij rho_i rho_j *)
			let term3  = (PPlus (entrycost, (PMonoterm (1, (Poly ((Eid bij), (Poly ((Mode rho1), (Mono (Mode rho2)))))))))) in
			(* rho_j - rho rho_j - rho_i rho_j + rho rho_i rho_j  + bij rho_i rho_j  - bij rho rho_i rho_j *)
			let diffidcost  = (PMinus (term3, (PMonoterm (1, (Poly ((Eid bij), (Poly ((Mode rho), Poly ((Mode rho1), (Mono (Mode rho2))))))))))) in
			let tpcost = PPlus (ecost, diffidcost) in
			tpcost

let rec num_atomic_exp = function
 | Lam (_,_,_,_,_, s) -> (num_atomic_stmt s)
 | Deref e -> num_atomic_exp e
 | _ -> 0

and num_atomic_stmt = function
    |Assign(x, e) -> 1 + (num_atomic_exp e)
    |Declassify(x, e) -> 1 + (num_atomic_exp e)
    |Update(e1, e2) -> 1 + (num_atomic_exp e2)  (* no e1 *)
    |Seq(s1, s2) ->  (num_atomic_stmt s1) + (num_atomic_stmt s2)
    |If(e, s1, s2) -> 1 + (num_atomic_stmt s1) + (num_atomic_stmt s2)
    |Call e ->  1 + num_atomic_exp e
    |While(e, s) -> 1 + (num_atomic_stmt s)
    |Output(x, e) ->  1
    |Set x	->  1
    |Skip -> 1

let compute_one_seq_trusted_cost (rho:mode) (rhoi:mode) (s:stmt) ecost =
			let sweight = num_atomic_stmt s in
			(* rho_i - rho rho_i *)
			let term1 = (PMinus (PMonoterm (sweight, (Mono (Mode rhoi))), (PMonoterm (sweight, (Poly ((Mode rho), ((Mono (Mode rhoi))))))))) in
			let tpcost = PPlus (ecost, term1) in
			tpcost

(* rho1 + rho2 -rho rho1 -rho rho2 *)
let  compute_if_entry_cost rho rho1 rho2 ecost =
			(* rho_1 - rho rho_1 *)
			let term1 = (PMinus (PMonoterm (1, (Mono (Mode rho1))), (PMonoterm (1, (Poly ((Mode rho), ((Mono (Mode rho1))))))))) in
			let term2 = (PPlus (term1, (PMonoterm (1, (Mono (Mode rho2)))))) in
			let term3 = (PPlus (term2, (PMonoterm (1, (Poly ((Mode rho), ((Mono (Mode rho2))))))))) in
			let tpcost = PPlus (ecost, term3) in
			tpcost

(* rho1 + rho2 -rho rho1 -rho rho2 *)
let  compute_if_trusted_cost rho rho1 rho2 s1 s2 ecost =
			let sweight1 = num_atomic_stmt s1 in
			let sweight2 = num_atomic_stmt s2 in
			(* rho_1 - rho rho_1 *)
			let term1 = (PMinus (PMonoterm (sweight1, (Mono (Mode rho1))), (PMonoterm (sweight1, (Poly ((Mode rho), ((Mono (Mode rho1))))))))) in
			let term2 = (PPlus (term1, (PMonoterm (sweight2, (Mono (Mode rho2)))))) in
			let term3 = (PPlus (term2, (PMonoterm (sweight2, (Poly ((Mode rho), ((Mono (Mode rho2))))))))) in
			let tpcost = PPlus (ecost, term3) in
			tpcost

(* -(1 - rho)rho1 rho2 b12 *) 
let  compute_if_diffid_cost  rho rho1 rho2 b12 ecost =
 			(* -rho_1 rho_2 b_12 + rho rho_1 rho_2 b_12 *)
 			let partialcost = (PMinus ((PMonoterm (1, (Poly ((Mode rho), (Poly ((Mode rho1), (Poly ((Mode rho2),(Mono (Eid b12)))))))))), 
								(PMonoterm (1, (Poly ((Mode rho1), (Poly ((Mode rho2),(Mono (Eid b12)))))))))) in
			let tpcost = PPlus (ecost, partialcost) in
			tpcost
(* rho' -rho rho' *)
let  compute_while_entry_cost rho rho' ecost =
			(* rho' - rho rho' *)
			let term1 = (PMinus (PMonoterm (1, (Mono (Mode rho'))), (PMonoterm (1, (Poly ((Mode rho), ((Mono (Mode rho'))))))))) in
			let tpcost = PPlus (ecost, term1) in
			tpcost

(* rho' -rho rho' *)
let  compute_while_trusted_cost rho rho' s ecost =
			let sweight = num_atomic_stmt s in
			(* rho' - rho rho'*)
			let term1 = (PMinus (PMonoterm (sweight, (Mono (Mode rho'))), (PMonoterm (sweight, (Poly ((Mode rho), ((Mono (Mode rho'))))))))) in
			let tpcost = PPlus (ecost, term1) in
			tpcost

