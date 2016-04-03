open Unix
open Printf
open Ast
open Helper
open Proplogic

exception ModeError of string
exception EidSelectionError of string

(* Execute solver and read back output in string *)
let read_process command =
  let buffer_size = 2048 in
  let buffer = Buffer.create buffer_size in
  let string = Bytes.create buffer_size in
  let in_channel = Unix.open_process_in command in
  let chars_read = ref 1 in
  while !chars_read <> 0 do
    chars_read := input in_channel string 0 buffer_size;
    Buffer.add_substring buffer string 0 !chars_read
  done;
  ignore (Unix.close_process_in in_channel);
  Buffer.contents buffer

let ismodevar xstr ms =
 let elems = ModeSet.elements ms in
 let rec check_rho_exists elemlist = begin match elemlist with
 |[] -> false
 |xs::tail -> begin match xs with
		| ModeVar (x, _) -> if x = xstr then true else	
					check_rho_exists tail
		| _ -> raise (ModeError "Can't have this mode in a mode variable")
	      end
 end
 in check_rho_exists elems 

 let iskillvar xstr klist =
 	List.exists (fun elm -> xstr = elm ) klist

let parse_model inp model: modesat =
 let xlist = Str.split (Str.regexp " ") inp in
 let rec loop xs model isbreak  = 
  match xs with
  | [] -> model
  | x::tail -> 
		(* Toysat has a different format. Gets \nv and \n*)
	    if isbreak then model 
	    else
		let xsign, pos, len' =
			let len = String.length x in
			let iszero = (Char.compare x.[0] '-') in
					if iszero = 0 then (0,1, len-1) else (1,0, len)
		 in
		let xstr' = String.sub x pos len' in
		let islastcharnv = (Char.compare xstr'.[len'-1] 'v') in
		let islastcharn = (Char.compare xstr'.[len'-1] '\n') in
		let xstr = if islastcharnv = 0 then
				(* Remove last 2 chars *)
				String.sub xstr' 0  (len' - 2)
			    else  
				if islastcharn=0 then
					String.sub xstr' 0  (len' - 1)
				else
					xstr'
		in
		(* Check if xstr is a mode variable or bij *)
		let model' = ModeSAT.add xstr xsign model
		in
		let isbreak = if islastcharn = 0 then true else false
		in loop tail model' isbreak
 in loop xlist model false

let extractsatmodel  inp : modesat =
  let pos = Str.search_forward (Str.regexp "OPTIMUM FOUND") inp 0 in
  let _ = Printf.printf "Position: %d\n" pos in
  let start = Str.search_forward (Str.regexp "v ") inp pos in
  
  let _ = Printf.printf "V Position: %d\n" start in
  let posend = Str.search_forward (Str.regexp "c ") inp start in
  let _ = Printf.printf "C Position: %d\n" posend in

  let extractsat = String.sub inp (start + 2) (posend - start -2) in
  let _ = Printf.printf "%s\n" extractsat  in
  parse_model extractsat ModeSAT.empty 


