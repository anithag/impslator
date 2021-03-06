(* variables *)
type var = string
type channel = char
(* (E, id), N, (rho, id) *)
type mode = Enclave of var list | Normal | ModeVar of var * var list

(* Set of mode variables *)
module ModeSet = Set.Make(struct
  type t = mode
  let compare = Pervasives.compare
end)

module VarSet = Set.Make(struct
  type t = var
  let compare = Pervasives.compare
end)

(* sets of condition variables *)
type cndset = VarSet.t

(* Not really a set. List of boolean variables 
   indicating enclave identifiers i.e., 
   eidset[i] = 1 implies i^th enclave 
   killset[i] = 1 implies i^th enclave is killed 
*)
type eidset = var list
type killset = var list

type varloc = Reg of var | Mem of int 

(* maps with variables and locations as keys *)
module VarLocMap = Map.Make(struct
  type t = varloc
  let compare = Pervasives.compare
end)

(* Base types *)
type basetype = 
    BtInt                             (* int *)
  | BtBool                            (* bool *)
  | BtString			      (* string *)
  | BtCond                            (* cond *)
  | BtPair of basetype * basetype     (* Tuple *)
  | BtArray of int * labeltype	      (* Array size and type *)
  | BtRef of labeltype		     (* tau ref *)
  | BtFunc of context * policy * cndset * context	     (* func *)

and
labeltype = basetype * policy   

and policy =
    Low
   |High
   |Top
   |Erase of policy * var * policy
 

(* expressions *)
and exp =
    Var of var                      (* x *)
  | Loc of int
  | Lam of context * policy * cndset * context * policy * stmt   (* (lambda(G_pre, p, {}, G_post).stmt)_q *)
  | Constant of int                 (* n *)
  | Literal of string               (* string constants *)
  | Tuple of exp * exp		    (* tuples *)
  | Array of int list		    (* list of locations: using int to denote locations *)
  | Plus of exp * exp               (* e1 + e2 *)
  | Modulo of exp * exp             (* e1 % e2 *)
  | True                            (* true *)
  | False                           (* false *)
  | Eq of exp * exp                 (* e1 = e2 *) 
  | Neq of exp * exp                (* e1 != e2 *) 
  | Lt of exp * exp                 (* e1 < e2 *) 
  | Fst of exp			    (* #1 (a, b) *)	
  | Snd of exp			    (* #2 (a, b) *)
  | Index of exp * exp		    (* a[idx], unlike C style, this expression results in lvalue only  *)
  | Deref of exp
  | Isunset of var
  
and
stmt = 
   If of exp * stmt * stmt           (* if e1 then e2 else e3 *)
  | Skip
  | Assign of var * exp
  | Declassify of var * exp
  | Update of exp * exp		     (* l <- e OR  l[idx] <- e *)  
  | Seq of (stmt list)  
  | While of  exp * stmt
  | Output of channel * exp
  | Call of exp
  | Set of var


(* typechecking environments - maps variables to types *)
and context = labeltype VarLocMap.t

(* Enclave Base types *)
type encbasetype = 
    EBtInt                             (* int *)
  | EBtBool                            (* bool *)
  | EBtString                          (* string *)
  | EBtPair of encbasetype * encbasetype       (* tuple *)
  | EBtArray of mode * int * enclabeltype      (* Array size and type *)
  | EBtCond of mode                    (* cond *)
  | EBtRef of mode * enclabeltype      (* tau ref *)
  | EBtFunc of mode* enccontext* killset*policy * cndset * enccontext*killset   (* func *)

and
enclabeltype = encbasetype * policy   

(* typechecking environments - maps variables to types *)
and  enccontext = enclabeltype VarLocMap.t

(*Quick Hack: Inefficient use of VarLocMap, we can use just use LocMap or something like that *)
type loctype = mode VarLocMap.t


type encexp =
    EVar of var                       (* x *)
  | ELoc of mode * int 		     (* l^ mode *)
  | ELam of mode * enccontext *killset * policy* cndset * enccontext*killset * policy*encstmt (* First mode|-lambda^mode(gpre,killpre, p,u, gpost, killpost, q, s) *)
  | EConstant of int                  (* n *)
  | ELiteral of string		      (* str literal *)
  | EArray of mode* (int list)	      (* []^mode *)
  | ETuple of encexp * encexp	      (* enc tuple *)
  | EPlus of encexp * encexp          (* e1 + e2 *)
  | EModulo of encexp * encexp        (* e1 % e2 *)
  | ETrue 			      (* true *)
  | EFalse 			       (* false *)
  | EEq of encexp * encexp             (* e1 = e2 *) 
  | ENeq of encexp * encexp            (* e1 != e2 *) 
  | ELt of encexp * encexp            (* e1 < e2 *) 
  | EFst of encexp
  | ESnd of encexp
  | EIndex of mode * encexp * encexp    (* a[idx], unlike C style, this expression results in lvalue only  *)
  | EDeref of encexp
  | EIsunset of var

and  encstmt = 
   EIf of encexp * encstmt * encstmt 
  |ESkip 
  |EAssign of var * encexp 
  |EDeclassify of var * encexp
  |EUpdate of encexp * encexp
  |ESeq of (encstmt list) 
  |EESeq of (encstmt list)
  |EWhile of encexp * encstmt
  |EOutput of channel * encexp
  |ECall of encexp
  |ESet of var

type progbody = Exp of exp | Stmt of stmt | EncExp of encexp
type program = context * stmt 


(* Translation Judgment *)
type translate = 
|TSkip of policy * context * cndset * context * stmt * mode * enccontext * killset * loctype * encstmt * enccontext * killset 
|TAssign  of policy * context * cndset * context * stmt * mode * enccontext * killset * loctype * var * translateexp * enccontext * killset 
|TDeclassify of policy * context * cndset * context * stmt * mode * enccontext * killset * loctype * var * translateexp * enccontext * killset 
|TUpdate of policy * context * cndset * context * stmt * mode * enccontext * killset * loctype * translateexp * translateexp * enccontext * killset 
|TOut of policy * context * cndset * context * stmt * mode * enccontext * killset * loctype * channel* translateexp* enccontext * killset 
|TSetcnd of policy * context * cndset * context * stmt * mode * enccontext * killset * loctype * var * enccontext * killset 
|TSeq of policy * context * cndset * context * stmt * mode * enccontext * killset * loctype * (translate * killset) list* enccontext * killset 
|TIf  of policy * context * cndset * context * stmt * mode * enccontext * killset * loctype * encexp * translate * translate * enccontext * killset 
|TWhile  of policy * context * cndset * context * stmt * mode * enccontext * killset * loctype * encexp * translate * enccontext * killset 
|TCall  of policy * context * cndset * context * stmt * mode * enccontext * killset * loctype * translateexp * enccontext * killset 

and translateexp = 
|TExp of  context * exp * labeltype * mode * enccontext * loctype * encexp * enclabeltype
|TLamExp of  context * exp * labeltype * mode * enccontext * loctype * translate* enclabeltype

(* Constraint Language *)
type tconstraint =
| ModeisN of mode * int 			(* μ = 1/0 *)
| ModeEqual of mode * mode 			(* μ1 = μ2 *)
| ModenotKilled of mode * killset  		(* μ \not \in K *)
| ModenotNimpliesEq of mode * mode   		(* μ = 1 -> μ = μ' *)
| ModenotNimpliesNoKill of mode * killset  	(* μ = 1 -> K'' = Ø *)
| ModeEqimpliesNoKill of mode * mode * killset 	(* μ1 = μ2 /\ μ1=1 -> K'' = Ø *)
| KillUnion  of killset * killset * killset 	(* K1 = K' U K'' *)
| KillIntersectEmpty of killset * killset  	(* K1 ∩ K2 = Ø *)
| EnclaveExitimpliesModeEq of mode * mode 	(* ~isVarLowContext -> μi = μi+1 *)
| EnclaveExitimpliesKill   of mode * killset 	(* ~isVarLowContext -> K'' = Ø *)
| KillEq  of killset * killset 			(* K1 = K2 *) 
| Killempty of killset 				(* K = Ø *)
| Enclaveid of mode				(* id1 =1 -> id2 = 0 /\ id3=0 ... *)
| UsedEnclave of killset * (mode list)		(* k[i] = 1 <-> \/ mulist[i] = 1 *)
| KillonlyUsedEnclave of killset * killset  	(* k[i] = 1 -> usedenclave[i] = 1 *)


module TConstraints = Set.Make (struct 
  type t = tconstraint
  let compare = Pervasives.compare
end)

