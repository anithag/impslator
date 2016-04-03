open Ast

(* Constraints below are in Propositional Logic Form *)

type mode_cond= (var * int) 
type eid_cond = (var * int) 
type constr_cond = 
 | Modecond of mode_cond  (* Represents mu = 1 *)
 | Eidcond of eid_cond    (* Represents id = 0/1 *)
 | Dnfclause of constr_cond list  

(* sets of pairs of types *)
module Constr = Set.Make(struct
  type t = constr_cond
  let compare = Pervasives.compare
end)

module Constr2 = Set.Make(struct
  type t = constr_cond * constr_cond
  let compare = Pervasives.compare
end)

(* constraints *)
type constr = Constr.t

(* Conditional constrains *)
type constr2 = Constr2.t

(* maps with mode variables as keys *)
module ModeVarMap = Map.Make(struct
  type t = var
  let compare = Pervasives.compare
end)

(* mode substitutions *)
type subst = mode ModeVarMap.t

(* maps with mode variables as keys *)
module ModeProgSet = Set.Make(struct
  type t = mode * progbody 
  let compare = Pervasives.compare
end)

(* evaluation environments *)
type modeenv = ModeProgSet.t

type modeset = ModeSet.t

type costvar = var

(* Polynomial representation for cost function *)
type polyterm =
 | Mono   of  costvar
 | Poly   of  costvar * polyterm


type polynomial = 
   |PConstant of int  (* e.g., 42 *)
   |PMonoterm of int * polyterm (* e.g., 42*x_1*x_2 *)
   |PUminusterm of int * polyterm (* e.g., -42*x_1*x_2 *)
   |PPlus     of polynomial * polynomial  (* 1 + 42*x_1*x_2  *)
   |PMinus    of polynomial * polynomial  (* 1 - 42*x_1*x_2  *)

type cost = polynomial
type totalcost = polynomial*polynomial 

(* Mode SAT *)
module ModeSAT = Map.Make(struct
  type t = costvar 
  let compare = Pervasives.compare
 end)
type modesat = int ModeSAT.t

(* Map bij to modes *)
module EnclaveidMap = Map.Make(struct
  type t = var
  let compare = Pervasives.compare
end)

type modepair = (mode * mode )
type enclaveidmap = modepair EnclaveidMap.t

module EnclaveidRevMap = Map.Make(struct
  type t = modepair
  let compare = Pervasives.compare
end)

type enclaveidrevmap = var EnclaveidRevMap.t

module EnclaveidConstraints = Map.Make(struct
  type t = mode
  let compare = Pervasives.compare
end)

type enclaveidconstraints = eidset EnclaveidConstraints.t
