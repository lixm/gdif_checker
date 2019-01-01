open Utils 
open Lexer
open Ast
open Parser
open Ggraph
open Eqana
open Brana
open Lvana
open Asst
open Valana 
open Typing

let usage = 
  "USAGE: gcifc [-pg] [-rc] [-eq] [-br] [-lv] [-asst] src_file"

exception Usage_error of string

let () = 
  let len_argarr = Array.length Sys.argv in 
  let arglst = List.tl (Array.to_list Sys.argv) in 
  try
    let opt_in_file = 
      Array.fold_left 
				(fun opt_file arg -> 
				 if String.get arg 0 <> '-' 
				 then 
					 if opt_file = None 
					 then Some arg 
					 else (let _ = raise (Usage_error "") in None)
				 else opt_file
				)
				None
				(Array.sub Sys.argv 1 (len_argarr - 1))
    in 
    let in_file = match opt_in_file with | Some file -> file | _ -> "" in
    let stm = open_stream in_file in
    try 
      let sc = { last_token=None; stm=stm } in 
      let sys = parse_sys sc in 
      let (pt_inv, pt_asst) = parse_inv_asst sc in 
      let (gnode, gmap) = g_graph_of_sys sys in 
      if List.mem "-pg" arglst then (
				print_endline (string_of_sys sys 2);          
				print_endline ("\n" ^ string_of_invariants pt_inv); 
				print_endline ("\n" ^ string_of_assertions pt_asst); 
				flush stdout
      );
      if List.mem "-rc" arglst then (
				print_endline (string_of_g_graph gnode); flush stdout
      );
      if List.mem "-eq" arglst then (
				let pt_eqs = eqana sys in 
				print_endline (string_of_pt_eqfms pt_eqs); flush stdout 
      );
      if List.mem "-br" arglst then (
				let pt_pt_brs = brana sys in 
				print_endline (string_of_pt_ptbrs pt_pt_brs ^ "\n"); 
				flush stdout
      );
      if List.mem "-lv" arglst then (
				let pt_lvs = lvana sys in 
				print_endline (string_of_ptlvs pt_lvs); flush stdout
      );
      if List.mem "-asst" arglst then (
				let z3_cfg = [("model", "true"); ("proof", "false")] in
				let z3_ctx = (Z3.mk_context z3_cfg) in 
				let pt_cond = post_cond_sys z3_ctx sys pt_inv pt_asst in 
				print_endline (string_of_pt_cond pt_cond); flush stdout
      );
			if List.mem "-val" arglst then (
				let z3_cfg = [("model", "true"); ("proof", "false")] in
				let z3_ctx = (Z3.mk_context z3_cfg) in 
				let pt_eqs = eqana sys in
				let pt_pt_brs = brana sys in 
				let pt_cond = post_cond_sys z3_ctx sys pt_inv pt_asst in
				let pt_val_be = get_val_fm_map pt_eqs pt_pt_brs pt_cond in
				print_endline (string_of_pt_val_be pt_val_be); flush stdout 
			); 
      if List.mem "-plc" arglst then (
				let z3_cfg = [("model", "true"); ("proof", "false")] in
				let z3_ctx = (Z3.mk_context z3_cfg) in 
				let (allprs, polmp_in) = parse_policies sc in
				let pt_eqs = eqana sys in 
				let pt_pt_brs = brana sys in 
				let pt_lvs = lvana sys in 
				let pt_cond = post_cond_sys z3_ctx sys pt_inv pt_asst in 
				let res = 
					well_typed_sys 
						z3_ctx gmap pt_eqs pt_pt_brs pt_cond pt_lvs polmp_in sys allprs 
				in 
				print_endline 
					("\nThe flow policies are " ^ 
						 (if res then "satisfied." else "not satisfied.")); flush stdout
      )
    with 
    | End_of_file -> close_in stm.chan 
    | e -> close_in_noerr stm.chan; raise e 
  with 
  | Usage_error _ -> print_endline (usage); flush stdout
						  
